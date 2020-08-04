#!/usr/bin/env python3

import errno
import json
import math
import os
import random
import select
import socket
import string
import subprocess
import sys
import time
import collections
import numpy as np
sys.path.append(os.path.join(os.path.dirname(__file__), '../submodules'))
import rsa
from base64 import b64decode
import getmac

from controller import Supervisor, Speaker

from player import Game
from image_frame_buffer import ImageFrameBuffer

import constants_1
import constants_2

kicktest = True

def get_distance(x1, y1, x2, y2):
    dist =  math.sqrt( \
                        math.pow(x1 - x2, 2) + \
                        math.pow(y1 - y2, 2))
    return dist

def random_string(length):
    """Generate a random string with the combination of lowercase and uppercase letters."""
    letters = string.ascii_letters
    return ''.join(random.choice(letters) for i in range(length))


def get_key(rpc):
    """The key is the first argument of the RPC."""
    first = rpc.find('"') + 1
    return rpc[first:rpc.find('"', first)]


def get_robot_name(self, color, id):
    name = self.constants.DEF_ROBOT_PREFIX
    if color == self.constants.TEAM_RED:
        name += 'R'
    elif color == self.constants.TEAM_BLUE:
        name += 'B'
    else:
        sys.stderr.write("Error: get_robot_name: Invalid team color.\n")
    name += str(id)
    return name


def get_role_name(self, role):
    if role == self.constants.TEAM_RED:
        return 'team red'
    if role == self.constants.TEAM_BLUE:
        return 'team blue'
    if role == self.constants.COMMENTATOR:
        return 'commentator'
    if role == self.constants.REPORTER:
        return 'reporter'
    sys.stderr.write("Error: get_role_name: Invalid role.\n")
    return ''


class TcpServer:
    def __init__(self, host, port):
        self.server = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.server.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.server.setblocking(False)
        self.server.bind((host, port))
        self.server.listen(5)
        self.connections = [self.server]
        self.unprocessedData = {}
        self.unprocessedData[self.server.fileno()] = ''

    def send_to_all(self, message):  # send message to all clients
        for client in self.connections:
            if client == self.server:
                continue
            self.send(client, message)

    def send(self, client, message):  # send message to a single client
        if client.fileno() == -1:  # was closed
            return
        try:
            client.sendall(message.encode())
        except ConnectionAbortedError:
            self.connections.remove(client)

    def spin(self, game_supervisor):  # handle asynchronous requests from clients
        def cleanup(s):
            print('Cleanup')
            if s in self.connections:
                self.connections.remove(s)
            s.close()
        while True:
            readable, writable, exceptional = select.select(self.connections, [], self.connections, 0)
            if not readable and not writable and not exceptional:
                return
            for s in readable:
                if s is self.server:
                    connection, client_address = s.accept()
                    connection.setblocking(False)
                    self.connections.append(connection)
                    self.unprocessedData[connection.fileno()] = ''
                    print('Accepted ', client_address)
                else:
                    success = True
                    data = ''
                    try:
                        while True:
                            d = s.recv(4096)
                            if not d:
                                break
                            data += d.decode()
                    except socket.error as e:
                        if e.args[0] == errno.EWOULDBLOCK:
                            success = True
                        else:
                            if e.args[0] != 10053:  # WSAECONNABORTED
                                print('Error caught: ', e.args[0])
                            success = False
                    if data and success:
                        self.unprocessedData[s.fileno()] = \
                            game_supervisor.callback(s, self.unprocessedData[s.fileno()] + data)
                    else:
                        print('Closing')
                        cleanup(s)
            for s in exceptional:
                print('Exceptional')
                cleanup(s)


class GameSupervisor(Supervisor):
    def __init__(self):
        Supervisor.__init__(self)
        self.title = self.getFromDef('DEF_AUDVIEW').getField('description').getSFString()
        self.type = 0 if self.title == "1" else 1
        if self.type == 0:
            self.constants = constants_1
        else:
            self.constants = constants_2
        self.basicTimeStep = int(self.getBasicTimeStep())
        self.timeStep = self.constants.PERIOD_MS
        self.waitReady = 0
        self.report = None

        self.speeds_buffer = [[0 for _ in range(30)],[0 for _ in range(30)]]
        
        # slider
        self.pre_fslider_height = [[0,0,0,0,0],[0,0,0,0,0]]
        self.fslider_count = [[0,0,0,0,0],[0,0,0,0,0]]
        self.fslider_trig = [[0,0,0,0,0],[0,0,0,0,0]]
        self.bslider_count = [[0,0,0,0,0],[0,0,0,0,0]]
        self.bslider_trig = [[0,0,0,0,0],[0,0,0,0,0]]
        self.t_brl = [[0,0,0,0,0],[0,0,0,0,0]]
        self.gk_trig = [0,0]
        # arm and leg
        self.arm_count = [[0,0,0,0,0],[0,0,0,0,0]]
        self.p_count = [[1,1,1,1,1],[1,1,1,1,1]]
        self.arm_speed = [[0,0,0,0,0],[0,0,0,0,0]]
        self.arm_speed2 = [[0,0,0,0,0],[0,0,0,0,0]]
        self.relocate_count = [[0,0,0,0,0],[0,0,0,0,0]]
        # multi view
        self.multi_view = False
        self.state_view = [0,0,0,0]
        self.pre_state_view = [0,0,0,0]
        # speaker
        self.speaker = self.getSpeaker("speaker")
        self.kick_sound_filter = 0
        # ball_possession
        self.ball_possession = [[False] * self.constants.NUMBER_OF_ROBOTS, [False] * self.constants.NUMBER_OF_ROBOTS]
        # keyboard
        self.keyboard = [False, False]
        # spotlight
        self.spotlight = self.getFromDef("DEF_BALLSPOTLIGHT")
        # dribble
        self.dribbler = None
        # crowdlock
        self.crowdlock = False
        self.crowdlock_time = 0

        self.receiver = self.getReceiver(self.constants.NAME_RECV)
        self.receiver.enable(self.constants.RECV_PERIOD_MS)

        self.cameraA = self.getCamera(self.constants.NAME_CAMA)
        self.cameraA.enable(self.constants.CAM_PERIOD_MS)
        self.cameraB = self.getCamera(self.constants.NAME_CAMB)
        self.cameraB.enable(self.constants.CAM_PERIOD_MS)
        self.imageFrameBufferA = ImageFrameBuffer(self.cameraA, self.constants.SUBIMAGE_NX, self.constants.SUBIMAGE_NY)
        self.imageFrameBufferB = ImageFrameBuffer(self.cameraB, self.constants.SUBIMAGE_NX, self.constants.SUBIMAGE_NY)

        self.cameraANode = self.getFromDef(self.constants.DEF_CAMA)
        self.cameraBNode = self.getFromDef(self.constants.DEF_CAMB)
        self.viewpointNode = self.getFromDef(self.constants.DEF_AUDVIEW)
        # DEF_GRASS is not visible to cam a and cam b, optional
        grass = self.getFromDef(self.constants.DEF_GRASS)
        grass.setVisibility(self.cameraANode, False)
        grass.setVisibility(self.cameraBNode, False)
        # BALLSHAPE is visible only to viewpoint, ORANGESHAPE is to cam_a and cam_b, mandatory
        ball = self.getFromDef(self.constants.DEF_BALLSHAPE)
        orange = self.getFromDef(self.constants.DEF_ORANGESHAPE)
        ball.setVisibility(self.cameraANode, False)
        ball.setVisibility(self.cameraBNode, False)
        if orange:
            orange.setVisibility(self.viewpointNode, False)
        # Stadium is visible only to viewpoint, optional
        stadium = self.getFromDef(self.constants.DEF_STADIUM)
        if stadium:
            stadium.setVisibility(self.cameraANode, False)
            stadium.setVisibility(self.cameraBNode, False)
        # Robot's black body is visible only to robots
        for team in self.constants.TEAMS:
            for id in range(self.constants.NUMBER_OF_ROBOTS):
                robot = self.getFromDef(get_robot_name(self, team, id))
                camBody = robot.getField('camBody')
                camBody0 = camBody.getMFNode(0)
                camBody0.setVisibility(self.viewpointNode, False)
        # Wall is visible only to robots
        wall = self.getFromDef(self.constants.DEF_WALL)
        if wall:
            wall.setVisibility(self.viewpointNode, False)
        # VisualWall is visible only to viewpoint, optional
        visual_wall = self.getFromDef(self.constants.DEF_VISWALL)
        if visual_wall:
            visual_wall.setVisibility(self.cameraANode, False)
            visual_wall.setVisibility(self.cameraBNode, False)
        # patches'
        for team in self.constants.TEAMS:
            for id in range(self.constants.NUMBER_OF_ROBOTS):
                robot = self.getFromDef(get_robot_name(self, team, id))
                patches = robot.getField('patches')
                # number patch for decoration exists
                if patches.getCount() == 3:
                    number = patches.getMFNode(0)
                    id_red = patches.getMFNode(1)
                    id_blue = patches.getMFNode(2)
                    number.setVisibility(self.cameraANode, False)
                    number.setVisibility(self.cameraBNode, False)
                    id_red.setVisibility(self.viewpointNode, False)
                    id_red.setVisibility(self.cameraBNode, False)
                    id_blue.setVisibility(self.viewpointNode, False)
                    id_blue.setVisibility(self.cameraANode, False)
                else:  # no decorations
                    id_red = patches.getMFNode(0)
                    id_blue = patches.getMFNode(1)
                    id_red.setVisibility(self.viewpointNode, True)  # useless ?
                    id_red.setVisibility(self.cameraBNode, False)
                    id_blue.setVisibility(self.viewpointNode, False)
                    id_blue.setVisibility(self.cameraANode, False)

        # comment buffer
        self.comments_ = collections.deque(maxlen=self.constants.NUM_COMMENTS)
        for t in range(self.constants.NUM_COMMENTS):  # fill with dummies
            self.comments_.append('')

    ## basic ##
    def step(self, timeStep, runTimer=False):
        for i in range(0, timeStep, self.basicTimeStep):
            if Supervisor.step(self, self.basicTimeStep) == -1:
                return -1
            if runTimer:
                self.time += self.basicTimeStep
            self.update_label()

    def get_role(self, rpc):
        key = get_key(rpc)
        for role in self.constants.ROLES:
            if role in self.role_info and 'key' in self.role_info[role] and self.role_info[role]['key'] == key:
                return role
        sys.stderr.write("Error: get_role: invalid key.\n")
        return -1

    def callback(self, client, message):
        unprocessed = ''
        if not message.startswith('aiwc.'):
            print('Error, AIWC RPC messages should start with "aiwc.".')
            return unprocessed

        # Handle concatenated messages
        data = message.split('aiwc.')
        for command in data:
            if not command:
                continue
            if not command.endswith(')'):
                unprocessed += 'aiwc.' + command
                continue
            role = self.get_role(command)
            self.role_client[role] = client
            if command.startswith('get_info('):
                print('Server receive aiwc.get_info from ' + get_role_name(self, role))
                if role == self.constants.TEAM_RED:
                    self.tcp_server.send(client, json.dumps(self.role_info[self.constants.TEAM_RED]))
                elif role == self.constants.TEAM_BLUE:
                    self.tcp_server.send(client, json.dumps(self.role_info[self.constants.TEAM_BLUE]))
                else:
                    self.tcp_server.send(client, json.dumps(self.role_info[self.constants.TEAM_RED]))
            elif command.startswith('ready('):
                self.ready[role] = True
                if role == self.constants.TEAM_RED:
                    self.imageFrameBufferA.reset()
                elif role == self.constants.TEAM_BLUE:
                    self.imageFrameBufferB.reset()
                print('Server receive aiwc.ready from ' + get_role_name(self, role))
            elif command.startswith('set_speeds('):
                if role > self.constants.TEAM_BLUE:
                    sys.stderr.write("Error, commentator and reporter cannot change robot speed.\n")
                    return unprocessed
                start = command.find('",') + 2
                end = command.find(')', start)
                speeds = command[start:end]
                speeds = [float(i) for i in speeds.split(',')]
                self.speeds_buffer[role] = speeds
                self.set_speeds(role, speeds)
            elif command.startswith('cont_num('):
                if role <=self.constants.TEAM_BLUE:
                    start = command.find('",') + 2
                    end = command.find(')', start)
                    cont_num = command[start:end]
                    self.light_control(role, cont_num)
            elif command.startswith('commentate('):
                if role != self.constants.COMMENTATOR:
                    sys.stderr.write("Error, only commentator can commentate.\n")
                    return unprocessed
                start = command.find('",') + 4
                comment = '[{:.2f}] {}'.format(self.time / 1000., command[start:-2])
                self.comments_.append(comment)
            elif command.startswith('report('):
                if role != self.constants.REPORTER:
                    sys.stderr.write("Error, only reporter can report.\n")
                    return unprocessed
                start = command.find('",') + 2
                self.report = command[start:-1]
            else:
                print('Server received unknown message', message)
        return unprocessed

    def publish_current_frame(self, reset_reason=None):
        frame_team_red = self.generate_frame(self.constants.TEAM_RED, reset_reason)  # frame also sent to commentator and reporter
        frame_team_blue = self.generate_frame(self.constants.TEAM_BLUE, reset_reason)
        for role in self.constants.ROLES:
            if role in self.role_client:
                frame = frame_team_blue if role == self.constants.TEAM_BLUE else frame_team_red
                self.tcp_server.send(self.role_client[role], json.dumps(frame))

    def generate_frame(self, team, reset_reason=None):
        opponent = self.constants.TEAM_BLUE if team == self.constants.TEAM_RED else self.constants.TEAM_RED
        frame = {}
        frame['time'] = self.getTime()
        frame['score'] = [self.score[team], self.score[opponent]]
        frame['reset_reason'] = reset_reason if reset_reason else self.reset_reason
        if team == self.constants.TEAM_BLUE:
            if frame['reset_reason'] == self.constants.SCORE_RED_TEAM:
                frame['reset_reason'] = Game.SCORE_OPPONENT
            elif frame['reset_reason'] == self.constants.SCORE_BLUE_TEAM:
                frame['reset_reason'] = Game.SCORE_MYTEAM
        frame['game_state'] = self.game_state
        frame['ball_ownership'] = True if self.ball_ownership == team else False
        frame['half_passed'] = self.half_passed
        frame['subimages'] = []
        imageFrameBuffer = self.imageFrameBufferA if team == self.constants.TEAM_RED else self.imageFrameBufferB
        for subImage in imageFrameBuffer.update_image(self.getTime()):
            frame['subimages'].append(subImage)
        frame['coordinates'] = [None] * 3
        for t in self.constants.TEAMS:
            frame['coordinates'][t] = [None] * self.constants.NUMBER_OF_ROBOTS
            c = team if t == self.constants.TEAM_RED else opponent
            for id in range(self.constants.NUMBER_OF_ROBOTS):
                frame['coordinates'][t][id] = [None] * 7
                pos = self.get_robot_posture(c, id)
                frame['coordinates'][t][id][0] = pos[0] if team == self.constants.TEAM_RED else -pos[0]
                frame['coordinates'][t][id][1] = pos[1] if team == self.constants.TEAM_RED else -pos[1]
                frame['coordinates'][t][id][2] = pos[2]
                if team == self.constants.TEAM_RED:
                    frame['coordinates'][t][id][3] = pos[3]
                else:
                    frame['coordinates'][t][id][3] = pos[3] + self.constants.PI if pos[3] < 0 else pos[3] - self.constants.PI
                frame['coordinates'][t][id][4] = self.robot[c][id]['active']
                frame['coordinates'][t][id][5] = self.robot[c][id]['touch']
                frame['coordinates'][t][id][6] = self.robot[c][id]['ball_possession']
        frame['coordinates'][2] = [None] * 3
        frame['coordinates'][2][0] = self.ball_position[0] if team == self.constants.TEAM_RED else -self.ball_position[0]
        frame['coordinates'][2][1] = self.ball_position[1] if team == self.constants.TEAM_RED else -self.ball_position[1]
        frame['coordinates'][2][2] = self.ball_position[2]
        frame['EOF'] = True
        return frame

    ## check state ##
    def get_corner_ownership(self):
        ball_x = self.get_ball_position()[0]
        ball_y = self.get_ball_position()[1]
        robot_count = [0, 0]
        robot_distance = [0, 0]
        s_x = 1 if ball_x > 0 else -1
        s_y = 1 if ball_y > 0 else -1
        # count the robots and distance from the ball in the corner region of concern
        for team in self.constants.TEAMS:
            for id in range(self.constants.NUMBER_OF_ROBOTS):
                if not self.robot[team][id]['active']:
                    continue
                robot_pos = self.get_robot_posture(team, id)
                x = robot_pos[0]
                y = robot_pos[1]
                # the robot is located in the corner region of concern
                if (s_x * x > self.constants.FIELD_LENGTH / 2 - self.constants.PENALTY_AREA_DEPTH) and \
                   (s_y * y > self.constants.PENALTY_AREA_WIDTH / 2):
                    distance_squared = (x - ball_x) * (x - ball_x) + (y - ball_y) * (y - ball_y)
                    robot_count[team] += 1
                    robot_distance[team] += math.sqrt(distance_squared)
        # decision - team with more robots near the ball gets the ownership
        if robot_count[0] > robot_count[1]:
            return 0
        elif robot_count[1] > robot_count[0]:
            return 1
        else:  # tie breaker - team with robots (within the decision region) closer to the ball on average gets the ownership
            if robot_distance[0] < robot_distance[1]:
                return 0
            elif robot_distance[1] < robot_distance[0]:
                return 1
            else:  # a total tie - the attacker team gets an advantage
                return 0 if ball_x > 0 else 1

    def get_pa_ownership(self):
        ball_x = self.get_ball_position()[0]
        ball_y = self.get_ball_position()[1]
        robot_count = [0, 0]
        robot_distance = [0, 0]
        s_x = 1 if ball_x > 0 else -1
        # count the robots and distance from the ball in the penalty area of concern
        for team in self.constants.TEAMS:
            for id in range(self.constants.NUMBER_OF_ROBOTS):
                if not self.robot[team][id]['active']:
                    continue
                robot_pos = self.get_robot_posture(team, id)
                x = robot_pos[0]
                y = robot_pos[1]
                # the robot is located in the corner region of concern
                if (s_x * x > self.constants.FIELD_LENGTH / 2 - self.constants.PENALTY_AREA_DEPTH) and \
                   (abs(y) < self.constants.PENALTY_AREA_WIDTH / 2):
                    distance_squared = (x - ball_x) * (x - ball_x) + (y - ball_y) * (y - ball_y)
                    robot_count[team] += 1
                    robot_distance[team] += math.sqrt(distance_squared)
        # decision - team with more robots near the ball gets the ownership
        if robot_count[0] > robot_count[1]:
            return 0
        elif robot_count[1] > robot_count[0]:
            return 1
        else:  # tie breaker - team with robots (within the decision region) closer to the ball on average gets the ownership
            if robot_distance[0] < robot_distance[1]:
                return 0
            elif robot_distance[1] < robot_distance[0]:
                return 1
            else:  # a total tie - the attacker team gets an advantage
                return 0 if ball_x > 0 else 1

    def check_penalty_area(self):
        ball_x = self.get_ball_position()[0]
        ball_y = self.get_ball_position()[1]
        robot_count = [0, 0]
        # check if the ball is not in the penalty area
        if (abs(ball_x) < self.constants.FIELD_LENGTH / 2 - self.constants.PENALTY_AREA_DEPTH) or \
           (abs(ball_y) > self.constants.PENALTY_AREA_WIDTH / 2):
            return False
        s_x = 1 if ball_x > 0 else -1
        # count the robots and distance from the ball in the penalty area of concern
        for team in self.constants.TEAMS:
            for id in range(self.constants.NUMBER_OF_ROBOTS):
                if not self.robot[team][id]['active']:
                    continue
                robot_pos = self.get_robot_posture(team, id)
                x = robot_pos[0]
                y = robot_pos[1]
                # the robot is located in the penalty area of concern
                if (s_x * x > self.constants.FIELD_LENGTH / 2 - self.constants.PENALTY_AREA_DEPTH) and \
                   (abs(y) < self.constants.PENALTY_AREA_WIDTH / 2):
                    robot_count[team] += 1
        if ball_x < 0:  # the ball is in Team Red's penalty area
            if robot_count[self.constants.TEAM_RED] > self.constants.PA_THRESHOLD_D:
                self.ball_ownership = self.constants.TEAM_BLUE
                return True
            if robot_count[self.constants.TEAM_BLUE] > self.constants.PA_THRESHOLD_A:
                self.ball_ownership = self.constants.TEAM_RED
                return True
        else:  # the ball is in Team Blue's penalty area
            if robot_count[self.constants.TEAM_BLUE] > self.constants.PA_THRESHOLD_D:
                self.ball_ownership = self.constants.TEAM_RED
                return True
            if robot_count[self.constants.TEAM_RED] > self.constants.PA_THRESHOLD_A:
                self.ball_ownership = self.constants.TEAM_BLUE
                return True
        return False

    def robot_in_field(self, team, id):
        robot_pos = self.get_robot_posture(team, id)
        x = robot_pos[0]
        y = robot_pos[1]
        if abs(y) < self.constants.GOAL_WIDTH / 2:
            if abs(x) > self.constants.FIELD_LENGTH / 2 + self.constants.GOAL_DEPTH:
                return False
            else:
                return True
        if abs(x) > self.constants.FIELD_LENGTH / 2:
            return False
        else:
            return True

    def ball_in_field(self):
        pos = self.get_ball_position()
        # checking with absolute values is sufficient since the field is symmetrical
        abs_x = abs(pos[0])
        abs_y = abs(pos[1])
        abs_z = abs(pos[2])

        if (abs_x > self.constants.FIELD_LENGTH / 2) and \
           (abs_y < self.constants.GOAL_WIDTH / 2) and \
           (abs_z >= 0.4):
            return False
        if (abs_x > self.constants.FIELD_LENGTH / 2 + self.constants.WALL_THICKNESS) and \
           (abs_y > self.constants.GOAL_WIDTH / 2 + self.constants.WALL_THICKNESS):
            return False
        if abs_y > self.constants.FIELD_WIDTH / 2 + self.constants.WALL_THICKNESS:
            return False
        # check triangular region at the corner
        cs_x = self.constants.FIELD_LENGTH / 2 - self.constants.CORNER_LENGTH
        cs_y = self.constants.FIELD_WIDTH / 2 + self.constants.WALL_THICKNESS
        ce_x = self.constants.FIELD_LENGTH / 2 + self.constants.WALL_THICKNESS
        ce_y = self.constants.FIELD_WIDTH / 2 - self.constants.CORNER_LENGTH
        if cs_x < abs_x and abs_x < ce_x:
            border_y = ce_y + (abs_x - ce_x) * (ce_y - cs_y) / (ce_x - cs_x)
            if abs_y > border_y:
                return False
        return True

    def any_object_nearby(self, target_x, target_y, target_r):
        # check ball position
        pos = self.get_ball_position()
        x = pos[0]
        y = pos[1]
        dist_sq = (target_x - x) * (target_x - x) + (target_y - y) * (target_y - y)
        # the ball is within the region
        if dist_sq < target_r * target_r:
            return True
        # check robot positions
        for team in self.constants.TEAMS:
            for id in range(self.constants.NUMBER_OF_ROBOTS):
                pos = self.get_robot_posture(team, id)
                x = pos[0]
                y = pos[1]
                dist_sq = (target_x - x) * (target_x - x) + (target_y - y) * (target_y - y)
                # a robot is within the region
                if dist_sq < target_r * target_r:
                    return True

    ## get informations ##
    def get_robot_touch_ball(self):
        rc = [[False] * self.constants.NUMBER_OF_ROBOTS, [False] * self.constants.NUMBER_OF_ROBOTS]
        while self.receiver.getQueueLength() > 0:
            message = self.receiver.getData()
            for team in self.constants.TEAMS:
                for id in range(self.constants.NUMBER_OF_ROBOTS):
                    cond = self.speeds_buffer[team][6*id+2] > 0
                    if message[2 * id + team] == 1:
                        rc[team][id] = True
            self.receiver.nextPacket()
        self.kick_sound(rc)
        return rc

    def flush_touch_ball(self):
        while self.receiver.getQueueLength() > 0:
            self.receiver.nextPacket()

    def get_robot_posture(self, team, id):
        position = self.robot[team][id]['node'].getPosition()
        orientation = self.robot[team][id]['node'].getOrientation()
        f = -1 if self.half_passed else 1
        x = position[0]
        y = -position[2]
        z = position[1]
        th = (self.constants.PI if self.half_passed else 0) + math.atan2(orientation[2], orientation[8]) + self.constants.PI / 2
        # Squeeze the orientation range to [-PI, PI]
        while th > self.constants.PI:
            th -= 2 * self.constants.PI
        while th < -self.constants.PI:
            th += 2 * self.constants.PI
        stand = orientation[4] > 0.8
        return [f * x, f * y, z, th, stand]

    def get_ball_position(self):
        f = -1 if self.half_passed else 1
        position = self.ball.getPosition()
        x = position[0]
        y = -position[2]
        z = position[1]
        return [f * x, f * y, z]

    def get_ball_velocity(self):
        v = self.ball.getVelocity()
        return math.sqrt(v[0] * v[0] + v[1] * v[1] + v[2] * v[2])

    ## actions ##
    def relocate_ball(self, pos):
        node = self.ball
        x = self.constants.BALL_POSTURE[pos][0]
        z = self.constants.BALL_POSTURE[pos][1]
        f = -1 if self.half_passed else 1
        translation = [f * x, 0.2, f * -z]
        rotation = [0, 1, 0, 0]
        node.getField('translation').setSFVec3f(translation)
        node.getField('rotation').setSFRotation(rotation)
        node.resetPhysics()

    def reset_ball(self, x, z):
        f = -1.0 if self.half_passed else 1.0
        self.ball.getField('translation').setSFVec3f([f * x, 1.5 * self.constants.BALL_RADIUS, -f * z])
        self.ball.getField('rotation').setSFRotation([0, 1, 0, 0])
        self.ball.resetPhysics()

        if self.multi_view:
            pn = self.getFromDef("DEF_AUDVIEW")
            pn.getField('orientation').setSFRotation([-1, 0, 0, 0.761])
            pn.getField('position').setSFVec3f([f * x, 5.27, 5.86 - f * z])

    def reset_robot(self, team, id, x, y, z, th):
        robot = self.getFromDef(get_robot_name(self, team, id))
        f = -1 if self.half_passed else 1
        translation = [f * x, y, f * -z]
        rotation = [0, 1, 0, th + (self.constants.PI if self.half_passed else 0)]

        al = robot.getField('axleLength').getSFFloat()
        h = robot.getField('height').getSFFloat()
        wr = robot.getField('wheelRadius').getSFFloat()

        lwTranslation = [-al / 2, (-h + 2 * wr) / 2, 0]
        rwTranslation = [al / 2, (-h + 2 * wr) / 2, 0]
        wheelRotation = [1, 0, 0, self.constants.PI / 2]

        robot.getField('translation').setSFVec3f(translation)
        robot.getField('rotation').setSFRotation(rotation)
        robot.getField('lwTranslation').setSFVec3f(lwTranslation)
        robot.getField('lwRotation').setSFRotation(wheelRotation)
        robot.getField('rwTranslation').setSFVec3f(rwTranslation)
        robot.getField('rwRotation').setSFRotation(wheelRotation)
        self.relocate_all(team, id)

        robot.resetPhysics()
        self.robot[team][id]['active'] = True
        self.robot[team][id]['touch'] = False
        self.robot[team][id]['ball_possession'] = False
        self.robot[team][id]['fall_time'] = self.time
        self.robot[team][id]['sentout_time'] = 0
        self.robot[team][id]['niopa_time'] = self.time  # not_in_opponent_penalty_area time
        self.robot[team][id]['ipa_time'] = self.time  # goalkeeper in_penalty_area time
        self.stop_robots()

    def reset(self, red_formation, blue_formation):
        # reset the ball
        if red_formation == self.constants.FORMATION_DEFAULT or red_formation == self.constants.FORMATION_KICKOFF:
            self.reset_ball(self.constants.BALL_POSTURE[self.constants.BALL_DEFAULT][0],
                            self.constants.BALL_POSTURE[self.constants.BALL_DEFAULT][1])
        elif red_formation == self.constants.FORMATION_GOALKICK_A:
            self.reset_ball(self.constants.BALL_POSTURE[self.constants.BALL_GOALKICK][0],
                            self.constants.BALL_POSTURE[self.constants.BALL_GOALKICK][1])
        elif red_formation == self.constants.FORMATION_GOALKICK_D:
            self.reset_ball(-self.constants.BALL_POSTURE[self.constants.BALL_GOALKICK][0],
                            self.constants.BALL_POSTURE[self.constants.BALL_GOALKICK][1])
        elif red_formation == self.constants.FORMATION_CAD_AD or red_formation == self.constants.FORMATION_CAD_DA:
            self.reset_ball(self.constants.BALL_POSTURE[self.constants.BALL_CORNERKICK][0],
                            self.constants.BALL_POSTURE[self.constants.BALL_CORNERKICK][1])
        elif red_formation == self.constants.FORMATION_CBC_AD or red_formation == self.constants.FORMATION_CBC_DA:
            self.reset_ball(self.constants.BALL_POSTURE[self.constants.BALL_CORNERKICK][0],
                            -self.constants.BALL_POSTURE[self.constants.BALL_CORNERKICK][1])
        elif red_formation == self.constants.FORMATION_CAD_AA or red_formation == self.constants.FORMATION_CAD_DD:
            self.reset_ball(-self.constants.BALL_POSTURE[self.constants.BALL_CORNERKICK][0],
                            -self.constants.BALL_POSTURE[self.constants.BALL_CORNERKICK][1])
        elif red_formation == self.constants.FORMATION_CBC_AA or red_formation == self.constants.FORMATION_CBC_DD:
            self.reset_ball(-self.constants.BALL_POSTURE[self.constants.BALL_CORNERKICK][0],
                            self.constants.BALL_POSTURE[self.constants.BALL_CORNERKICK][1])
        elif red_formation == self.constants.FORMATION_PENALTYKICK_A:
            self.reset_ball(self.constants.BALL_POSTURE[self.constants.BALL_PENALTYKICK][0],
                            self.constants.BALL_POSTURE[self.constants.BALL_PENALTYKICK][1])
        elif red_formation == self.constants.FORMATION_PENALTYKICK_D:
            self.reset_ball(-self.constants.BALL_POSTURE[self.constants.BALL_PENALTYKICK][0],
                            self.constants.BALL_POSTURE[self.constants.BALL_PENALTYKICK][1])
        elif red_formation == self.constants.FORMATION_KICKTEST:
            self.reset_ball(self.constants.BALL_POSTURE[self.constants.BALL_KICKTEST][0],
                            self.constants.BALL_POSTURE[self.constants.BALL_KICKTEST][1])

        # reset the robots
        for team in self.constants.TEAMS:
            if team == self.constants.TEAM_RED:
                s = 1
                a = 0
                formation = red_formation
            else:
                s = -1
                a = self.constants.PI
                formation = blue_formation
            for id in range(self.constants.NUMBER_OF_ROBOTS):
                self.reset_robot(team, id,
                                 self.constants.ROBOT_FORMATION[formation][id][0] * s,
                                 0.09 / 2,
                                 self.constants.ROBOT_FORMATION[formation][id][1] * s,
                                 self.constants.ROBOT_FORMATION[formation][id][2] + a - self.constants.PI / 2)

        # reset recent touch
        self.recent_touch = [[False] * self.constants.NUMBER_OF_ROBOTS, [False] * self.constants.NUMBER_OF_ROBOTS]
        self.deadlock_time = self.time
        # flush touch packet
        self.flush_touch_ball()
        # reset slider, arm and leg
        self.relocate_all_every()

    def lock_all_robots(self, locked):
        for t in self.constants.TEAMS:
            for id in range(self.constants.NUMBER_OF_ROBOTS):
                self.robot[t][id]['active'] = not locked
        if locked:
            self.relocate_all_every()

    def stop_robots(self):
        for t in self.constants.TEAMS:
            for id in range(self.constants.NUMBER_OF_ROBOTS):
                self.relocate_arm_leg(t, id)
                self.arm_count[t][id] = 0
                self.arm_speed[t][id] = 0
                self.relocate_count[t][id] = 0
            self.set_speeds(t, [0, 0, 0, 0, 0, 0, 0, 0,
                                0, 0, 0, 0, 0, 0, 0, 0,
                                0, 0, 0, 0, 0, 0, 0, 0,
                                0, 0, 0, 0, 0, 0, 0, 0,
                                0, 0, 0, 0, 0, 0, 0, 0])

    def send_to_foulzone(self, team, id):
        f = -1 if self.half_passed else 1
        s = 1 if team == 0 else -1
        translation = [f * self.constants.ROBOT_FOUL_POSTURE[id][0] * s,
                       0.09 / 2,
                       f * -self.constants.ROBOT_FOUL_POSTURE[id][1] * s]
        angle = self.constants.PI if self.half_passed else 0
        angle += self.constants.ROBOT_FOUL_POSTURE[id][2]
        angle += 0 if team == 0 else self.constants.PI
        angle -= self.constants.PI / 2
        rotation = [0, 1, 0, angle]

        node = self.robot[team][id]['node']
        al = node.getField('axleLength').getSFFloat()
        h = node.getField('height').getSFFloat()
        wr = node.getField('wheelRadius').getSFFloat()
        lwTranslation = [-al / 2, (-h + 2 * wr) / 2, 0]
        rwTranslation = [al / 2, (-h + 2 * wr) / 2, 0]
        wheelRotation = [1, 0, 0, self.constants.PI / 2]
        custom_0 = '0 0 0 0 0 0 0 0' if self.type == 1 else '0 0 0 0 0'
        
        node.getField('translation').setSFVec3f(translation)
        node.getField('rotation').setSFRotation(rotation)
        node.getField('customData').setSFString(custom_0)
        node.getField('lwTranslation').setSFVec3f(lwTranslation)
        node.getField('lwRotation').setSFRotation(wheelRotation)
        node.getField('rwTranslation').setSFVec3f(rwTranslation)
        node.getField('rwRotation').setSFRotation(wheelRotation)
        self.relocate_all(team, id)
        node.resetPhysics()

    def return_to_field(self, team, id):
        robot = self.robot[team][id]['node']
        f = -1 if self.half_passed else 1
        s = 1 if team == 0 else -1
        translation = [f * self.constants.ROBOT_FORMATION[self.constants.FORMATION_DEFAULT][id][0] * s,
                       0.09 / 2,
                       f * -self.constants.ROBOT_FORMATION[self.constants.FORMATION_DEFAULT][id][1] * s]
        angle = self.constants.PI if self.half_passed else 0
        angle += self.constants.ROBOT_FORMATION[self.constants.FORMATION_DEFAULT][id][2]
        angle += 0 if team == 0 else self.constants.PI
        angle -= self.constants.PI / 2
        rotation = [0, 1, 0, angle]
        al = robot.getField('axleLength').getSFFloat()
        h = robot.getField('height').getSFFloat()
        wr = robot.getField('wheelRadius').getSFFloat()
        lwTranslation = [-al / 2, (-h + 2 * wr) / 2, 0]
        rwTranslation = [al / 2, (-h + 2 * wr) / 2, 0]
        wheelRotation = [1, 0, 0, self.constants.PI / 2]
        robot.getField('translation').setSFVec3f(translation)
        robot.getField('rotation').setSFRotation(rotation)
        robot.getField('lwTranslation').setSFVec3f(lwTranslation)
        robot.getField('lwRotation').setSFRotation(wheelRotation)
        robot.getField('rwTranslation').setSFVec3f(rwTranslation)
        robot.getField('rwRotation').setSFRotation(wheelRotation)
        self.relocate_all(team, id)
        robot.resetPhysics()

    ## label ##
    def update_label(self):
        seconds = self.time / 1000.0
        minutes = seconds // 60
        seconds -= minutes * 60
        if not self.half_passed:
            self.setLabel(1, '%d:%d' % (self.score[0], self.score[1]), 0.48, 0.9, 0.10, 0x00000000, 0, 'Arial')
            self.setLabel(0, '%d:%05.2f (1st half)' % (minutes, seconds), 0.45, 0.95, 0.1, 0x00000000, 0, 'Arial')
        else:
            minutes += self.add_minutes
            seconds += self.add_seconds
            self.setLabel(1, '%d:%d' % (self.score[1], self.score[0]), 0.48, 0.9, 0.10, 0x00000000, 0, 'Arial')
            self.setLabel(0, '%d:%05.2f (2nd half)' % (minutes, seconds), 0.45, 0.95, 0.1, 0x00000000, 0, 'Arial')

        comments_start = 2

        for t in range(self.constants.NUM_COMMENTS):
            self.setLabel(comments_start + t, self.comments_[t], 0.01, 0.01 + 0.04 * t, 0.08, 0x00000000, 0, 'Arial')

    ## camera ##
    def mark_half_passed(self):
        self.cameraANode.getField('rotation').setSFRotation([0, 0, 1, self.constants.PI])
        self.cameraBNode.getField('rotation').setSFRotation([0, 0, 1, 0])

    def episode_restart(self):
        self.cameraANode.getField('rotation').setSFRotation([0, 0, 1, 0])
        self.cameraBNode.getField('rotation').setSFRotation([0, 0, 1, self.constants.PI])

    ## speed ##
    def set_speeds(self, team, speeds):
        letter = 'R' if team == self.constants.TEAM_RED else 'B'
        def_robot_prefix = self.constants.DEF_ROBOT_PREFIX + letter
        for id in range(self.constants.NUMBER_OF_ROBOTS):
            robot = self.getFromDef(def_robot_prefix + str(id))
            if self.robot[team][id]['active']:
                self.set_fs_height(team, id)
                fs_speed = 0
                if self.ball_possession[team][id] == True:
                    fs_speed = self.check_fslider(speeds, team, id)
                if id == 0:
                    bs_speed = self.check_bslider_GK(speeds, team, 0)
                else:
                    bs_speed = self.check_bslider(speeds, team, id)
                if self.type == 0:
                    arm_leg_speed = 0 if self.gk_trig[team] != 0 else self.move_arm_leg_1(speeds, team, id)
                    robot.getField('customData').setSFString(
                        "%f %f %f %f %f" % (speeds[id * 6] / self.constants.WHEEL_RADIUS[id], speeds[id * 6 + 1] / self.constants.WHEEL_RADIUS[id],
                                            fs_speed, bs_speed, arm_leg_speed)
                    )
                else:
                    arm_leg_speed = [0,0,0,0] if self.gk_trig[team] != 0 else self.move_arm_leg_2(speeds, team, id)
                    robot.getField('customData').setSFString(
                        "%f %f %f %f %f %f %f %f" % (speeds[id * 6] / self.constants.WHEEL_RADIUS[id], speeds[id * 6 + 1] / self.constants.WHEEL_RADIUS[id],
                                            fs_speed, bs_speed, arm_leg_speed[0], arm_leg_speed[1], arm_leg_speed[2], arm_leg_speed[3])
                    )
            else:
                self.arm_count[team][id] = 0
                self.relocate_arm_leg(team, id)
                custom_0 = '0 0 0 0 0 0 0 0' if self.type == 1 else '0 0 0 0 0'
                robot.getField('customData').setSFString(custom_0)                

    ## arm_leg and sliders ##
    def move_arm_leg_1(self, speeds, team, id):
        m_speed = 3*(abs(speeds[id * 6])+abs(speeds[id * 6 + 1]))
        speed_arm_leg = 0
        if (self.arm_count[team][id] % self.p_count[team][id] == 0):
            self.relocate_count[team][id] += 1
            if (self.relocate_count[team][id] == 10):
                self.relocate_count[team][id] = 0
                self.relocate_arm_leg(team, id)
            if (m_speed < 1):
                self.arm_count[team][id] = 0
            self.arm_count[team][id] = 0
            i_speed = int(m_speed)
            if (i_speed < 3):
                self.arm_speed[team][id] = 0
            elif (i_speed < 5):
                self.arm_speed[team][id] = i_speed
            elif (i_speed < 8):
                self.arm_speed[team][id] = 6
            elif (i_speed < 10):
                self.arm_speed[team][id] = i_speed
            else:
                self.arm_speed[team][id] = 12
            if (self.arm_speed[team][id] == 0):
                self.p_count[team][id] = 4
            else:
                self.p_count[team][id] = 72*2/self.arm_speed[team][id]

        if ((self.arm_count[team][id] % self.p_count[team][id] < self.p_count[team][id]/4) or
            (self.arm_count[team][id] % self.p_count[team][id] >= self.p_count[team][id]*3/4) ):
            speed_arm_leg = self.arm_speed[team][id]
        else:
            speed_arm_leg = -self.arm_speed[team][id]
            
        self.arm_count[team][id] += 1

        return speed_arm_leg

    def move_arm_leg_2(self, speeds, team, id):
        m_speed = abs(3*((speeds[id * 6])+(speeds[id * 6 + 1])))
        speed_arm_leg1 = 0
        speed_arm_leg2 = 0
        speed_arm_leg3 = 0
        speed_arm_leg4 = 0
        if (self.arm_count[team][id] % self.p_count[team][id] == 0):
            self.relocate_count[team][id] += 1
            if (self.relocate_count[team][id] == 10):
                self.relocate_count[team][id] = 0
                self.relocate_arm_leg(team, id)
            if (m_speed < 1):
                self.arm_count[team][id] = 0
            self.arm_count[team][id] = 0
            i_speed = int(m_speed)
            if (i_speed < 3):
                self.arm_speed[team][id] = 0
            elif (i_speed < 5):
                self.arm_speed[team][id] = i_speed
            elif (i_speed < 8):
                self.arm_speed[team][id] = 6
            elif (i_speed < 10):
                self.arm_speed[team][id] = i_speed
            else:
                self.arm_speed[team][id] = 12
            if (self.arm_speed[team][id] == 0):
                self.p_count[team][id] = 4
            else:
                self.p_count[team][id] = 72*2/self.arm_speed[team][id]

        temp = self.arm_count[team][id] % self.p_count[team][id]

        if (temp < self.p_count[team][id]/4):
            speed_arm_leg1 = 1.5*self.arm_speed[team][id]
            speed_arm_leg2 = -self.arm_speed[team][id]
            speed_arm_leg3 = -self.arm_speed[team][id]
            speed_arm_leg4 = 0
        elif (temp < self.p_count[team][id]*2/4):
            speed_arm_leg1 = -1.5*self.arm_speed[team][id]
            speed_arm_leg2 = self.arm_speed[team][id]
            speed_arm_leg3 = self.arm_speed[team][id]
            speed_arm_leg4 = 0
        elif (temp < self.p_count[team][id]*3/4):
            speed_arm_leg1 = -self.arm_speed[team][id]
            speed_arm_leg2 = 1.5*self.arm_speed[team][id]
            speed_arm_leg3 = 0
            speed_arm_leg4 = -self.arm_speed[team][id]
        else:
            speed_arm_leg1 = self.arm_speed[team][id]
            speed_arm_leg2 = -1.5*self.arm_speed[team][id]
            speed_arm_leg3 = 0
            speed_arm_leg4 = self.arm_speed[team][id]
            
        self.arm_count[team][id] += 1

        return speed_arm_leg1, speed_arm_leg2, speed_arm_leg3, speed_arm_leg4

    def relocate_arm_leg(self, team, id):
        self.arm_count[team][id] = 0
        robot = self.robot[team][id]['node']

        sliderRotation = [1, 0, 0, 0]
        laTranslation = [0, 0.07, 0]
        raTranslation = [0, 0.07, 0]
        llTranslation = [0, 0.01, 0]
        rlTranslation = [0, 0.01, 0]

        robot.getField('laTranslation').setSFVec3f(laTranslation)
        robot.getField('raTranslation').setSFVec3f(raTranslation)
        robot.getField('laRotation').setSFRotation(sliderRotation)
        robot.getField('raRotation').setSFRotation(sliderRotation)
        robot.getField('llTranslation').setSFVec3f(llTranslation)
        robot.getField('rlTranslation').setSFVec3f(rlTranslation)
        robot.getField('llRotation').setSFRotation(sliderRotation)
        robot.getField('rlRotation').setSFRotation(sliderRotation)
        if self.type == 1:
            robot.getField('llTranslation2').setSFVec3f(llTranslation)
            robot.getField('rlTranslation2').setSFVec3f(rlTranslation)
            robot.getField('llRotation2').setSFRotation(sliderRotation)
            robot.getField('rlRotation2').setSFRotation(sliderRotation)
        robot.resetPhysics()

    def relocate_arm_leg_all(self):
        for team in self.constants.TEAMS:
            for id in range(self.constants.NUMBER_OF_ROBOTS):
                self.relocate_arm_leg(team, id)

    def check_fslider(self, speeds, team, id):
        fs_speed = max(min(speeds[id * 6 + 2],10),0)
        t_frl = 4
        m_fs = 0.2
        if (self.fslider_trig[team][id] == 0) and (fs_speed > 0):
            self.fslider_trig[team][id] = 1

        if (self.fslider_trig[team][id] == 1):
            self.fslider_count[team][id] += 1
            if (self.fslider_count[team][id] <= 2):
                fs_speed = fs_speed
            elif (self.fslider_count[team][id] < t_frl):
                fs_speed = -3
            else:
                fs_speed = 0
                if (self.fslider_count[team][id] == t_frl):
                    self.relocate_fslider(team, id)
                elif (self.fslider_count[team][id] == 20):
                    self.fslider_count[team][id] = 0
                    self.fslider_trig[team][id] = 0

        robot_pos = self.get_robot_posture(team, id)
        if team == 0 and robot_pos[0] > 3 and abs(robot_pos[1]) < 0.9:
            fs_speed = 0
        if team == 1 and robot_pos[0] < -3 and abs(robot_pos[1]) < 0.9:
            fs_speed = 0

        robot = self.robot[team][id]['node']
        cond = (abs(robot.getField('fsTranslation').getSFVec3f()[2]) > 0.01)
        if (self.fslider_trig[team][id] == 0) and cond:
            self.relocate_fslider(team,id)

        return m_fs * fs_speed

    def relocate_fslider(self, team, id):
        robot = self.robot[team][id]['node']

        fs_height = self.pre_fslider_height[team][id]
        sliderRotation = [1, 0, 0, 0]
        fsTranslation = [0, fs_height, 0]

        robot.getField('fsTranslation').setSFVec3f(fsTranslation)
        robot.getField('fsRotation').setSFRotation(sliderRotation)
        robot.resetPhysics()

    def set_fs_height(self, team, id):
        robot = self.robot[team][id]['node']

        fs_height = -max(0,min(self.speeds_buffer[team][6*id+3],10))
        if fs_height != 0 :
            fs_height = fs_height*0.0045-0.005
        sliderRotation = [1, 0, 0, 0]
        fsTranslation = [0, fs_height, 0]

        if (self.pre_fslider_height[team][id] != fs_height):
            self.pre_fslider_height[team][id] = fs_height

            robot.getField('fsTranslation').setSFVec3f(fsTranslation)
            robot.getField('fsRotation').setSFRotation(sliderRotation)
            robot.resetPhysics()

    def check_bslider(self, speeds, team, id):
        bs_speed = max(min(speeds[id * 6 + 4],10),0)
        t_brls = [
            [5,5,6,7,7,8,8,9,10,11,11],
            [5,5,6,7,7,8,8,9,10,10,11],
            [5,5,6,7,7,8,8,9,10,10,11],
            [5,5,6,6,7,7,8,9,10,10,11],
            [5,5,6,6,7,7,8,9,10,10,11]
        ]
        m_bs = 0.24
        if ((self.bslider_trig[team][id] == 0) and (bs_speed > 0)):
            self.bslider_trig[team][id] = 1
            self.t_brl[team][id] = t_brls[id][int(bs_speed)]

        if (self.bslider_trig[team][id] == 1):
            self.bslider_count[team][id] += 1
            if (self.bslider_count[team][id] <= 2):
                bs_speed = bs_speed
            elif (self.bslider_count[team][id] < self.t_brl[team][id]):
                bs_speed = -2
            else:
                bs_speed = 0
                if (self.bslider_count[team][id] == self.t_brl[team][id]):
                    self.relocate_bslider(team, id)
                elif (self.bslider_count[team][id] == 20):
                    self.bslider_count[team][id] = 0
                    self.bslider_trig[team][id] = 0

        robot = self.robot[team][id]['node']
        cond = (abs(robot.getField('bsTranslation').getSFVec3f()[1] + 0.037) > 0.0025)
        if (self.bslider_trig[team][id] == 0) and cond:
            self.relocate_bslider(team,id)

        return m_bs * bs_speed

    def check_bslider_GK(self, speeds, team, id):
        bs_speed = max(min(speeds[id * 6 + 4],10),0)
        t_brls = [9,11,11,7,7,8,8,9,10,11,11]
        m_bs = 0.24
        if ((self.bslider_trig[team][id] == 0) and (self.gk_trig[team]==0) and (bs_speed > 0)):
            self.bslider_trig[team][id] = 1
            self.gk_trig[team] = speeds[4] if 1 <= speeds[4] <= 3 else 0
            self.t_brl[team][id] = t_brls[int(bs_speed)]
        if self.type == 1 and (self.gk_trig[team] == 1):
            self.bslider_count[team][id] += 1
            if (self.bslider_count[team][id] <=2):
                bs_speed = bs_speed
            elif (self.bslider_count[team][id] < t_brls[0]):
                bs_speed = -2
            elif (self.bslider_count[team][id] == t_brls[0]):
                bs_speed = 0
                self.relocate_bslider(team, id)
            elif (self.bslider_count[team][id] <= 10):
                bs_speed = 0
            elif (self.bslider_count[team][id] < 13):
                bs_speed = self.gk_trig[team]
            elif (self.bslider_count[team][id] < 15):
                bs_speed = -2
            elif (self.bslider_count[team][id] == 15):
                bs_speed = 0
                self.relocate_bslider(team, id)
            elif (self.bslider_count[team][id] < 20):
                bs_speed = 0
            elif (self.bslider_count[team][id] == 20):
                bs_speed = 0
                self.bslider_count[team][id] = 0
                self.gk_trig[team] = 0

        elif (self.bslider_trig[team][id] == 1):
            self.bslider_count[team][id] += 1
            if (self.bslider_count[team][id] <= 2):
                bs_speed = bs_speed
            elif (self.bslider_count[team][id] < self.t_brl[team][id]):
                bs_speed = -2
            else:
                bs_speed = 0
                if (self.bslider_count[team][id] == self.t_brl[team][id]):
                    self.relocate_bslider(team, id)
                elif (self.bslider_count[team][id] == 20):
                    self.bslider_count[team][id] = 0
                    self.bslider_trig[team][id] = 0
                    self.gk_trig[team] = 0

        robot = self.robot[team][id]['node']

        if self.gk_trig[team] > 0:
            if (self.bslider_count[team][id] == 1):
                self.relocate_arm_leg(team, id)
                if self.type == 0:
                    robot.getField('laTranslation').setSFVec3f([0, 0.19, 0.025])
                    robot.getField('raTranslation').setSFVec3f([0, 0.19, 0.025])
                else:
                    robot.getField('laTranslation').setSFVec3f([0, 0.495, 0.005])
                    robot.getField('raTranslation').setSFVec3f([0, 0.495, 0.005])
                robot.getField('laRotation').setSFRotation([1, 0, 0, 3.14])
                robot.getField('raRotation').setSFRotation([1, 0, 0, 3.14])
            elif (self.bslider_count[team][id] == 15):
                self.relocate_arm_leg(team, id)

        cond = (abs(robot.getField('bsTranslation').getSFVec3f()[1] + 0.037) > 0.0025)
        cond_b = (abs(robot.getField('bbsTranslation').getSFVec3f()[1] + 0.037) > 0.0025)
        cond_r = (abs(robot.getField('rbsTranslation').getSFVec3f()[1] + 0.037) > 0.0025)
        cond_l = (abs(robot.getField('lbsTranslation').getSFVec3f()[1] + 0.037) > 0.0025)
        cond_a = cond or cond_b or cond_r or cond_l
        if (self.bslider_trig[team][id] == 0) and (self.gk_trig[team] == 0) and cond_a:
            self.relocate_bslider(team,id)

        return m_bs * bs_speed

    def relocate_bslider(self, team, id):
        robot = self.robot[team][id]['node']

        sliderRotation = [1, 0, 0, 0]
        bsTranslation = [0, -0.037, 0]

        if id == 0:
            robot.getField('bbsTranslation').setSFVec3f(bsTranslation)
            robot.getField('rbsTranslation').setSFVec3f(bsTranslation)
            robot.getField('lbsTranslation').setSFVec3f(bsTranslation)

        robot.getField('bsTranslation').setSFVec3f(bsTranslation)
        robot.getField('bsRotation').setSFRotation(sliderRotation)
        robot.resetPhysics()

    def relocate_all(self, team, id):
        self.relocate_bslider(team, id)
        self.bslider_count[team][id] = 0
        self.relocate_fslider(team, id)
        self.fslider_count[team][id] = 0
        self.relocate_arm_leg(team, id)
        self.arm_count[team][id] = 0
        self.arm_speed[team][id] = 0
        self.relocate_count[team][id] = 0

    def relocate_all_every(self):
        for team in self.constants.TEAMS:
            for id in range(self.constants.NUMBER_OF_ROBOTS):
                self.relocate_all(team, id)

    ## ball possession ##
    def get_ball_possession(self):
        rc = [[False] * self.constants.NUMBER_OF_ROBOTS, [False] * self.constants.NUMBER_OF_ROBOTS]
        for team in self.constants.TEAMS:
            for id in range(self.constants.NUMBER_OF_ROBOTS):
                if self.robot_in_field(team, id):
                    rc[team][id] = self.check_ball_poss(team, id)
        return rc

    def check_ball_poss(self, team, id):
        ball_x = self.get_ball_position()[0]
        ball_y = self.get_ball_position()[1]
        ball_z = self.get_ball_position()[2]
        robot_pos = self.get_robot_posture(team, id)
        x = robot_pos[0]
        y = robot_pos[1]
        z = robot_pos[2]
        th = robot_pos[3]

        theta = th
        if (th > self.constants.PI):
            theta -= 2*self.constants.PI
        d_theta = abs(theta - math.atan2(ball_y-y, ball_x-x))
        if (d_theta > self.constants.PI):
            d_theta -= 2*self.constants.PI
        dist = math.sqrt((ball_y - y)*(ball_y - y)+(ball_x - x)*(ball_x - x))
        robot = self.robot[team][id]['node']
        v_r = robot.getVelocity()
        v_b = self.ball.getVelocity()
        v = [v_r[0] - v_b[0], v_r[1] - v_b[1], v_r[2] - v_b[2]]
        speed = math.sqrt(v[0] * v[0] + v[1] * v[1] + v[2] * v[2])
        add = 0
        if (speed < 0.5):
            add = 0.5 * 0.13
        else:
            add = speed * 0.13
        d_range = self.constants.ROBOT_SIZE[id]/2 + self.constants.BALL_RADIUS + add
            
        if ((dist < d_range) and (abs(d_theta) < self.constants.PI/4) and (abs(z - ball_z) < 0.01)):
            return True
        else:
            return False

    ## viewpoint ##
    def change_view(self):
        if self.multi_view:
            pn = self.getFromDef("DEF_AUDVIEW")
            x = self.get_ball_position()[0]
            y = self.get_ball_position()[1]
            z = self.get_ball_position()[2]
            f = -1 if self.half_passed else 1
            sc = 1 if self.type == 0 else 1.3
            orientation = [
                    [-1.00,  0.00,  0.00,  0.76],   # normal
                    [-0.17,  0.97,  0.17,  1.60],   # right
                    [ 1.00,  0.00,  0.00,  4.71],   # top
                    [-0.17, -0.97, -0.17,  1.60],   # left
                    [ 1.00,  0.00,  0.00,  4.71],   # kickoff
            ]
            position = [
                    [f * x, 5.27 * sc, 5.86 * sc - f * y], [ 9.43,  3.10 * sc,  0.00],
                    [ 0.00, 12.00 * sc,  0.00], [-9.43,  3.10 * sc,  0.00], [ 0.00,  6.00 * sc,  0.00]
            ]

            for i in range(4):
                if (self.game_state == i + 1):
                   self.state_view[i] = 1
                if (self.state_view[i] == 1):
                    period = [1000,750,1500,1500]
                    if (i == 0) : state_time = self.kickoff_time
                    elif (i == 1) : state_time = self.goalkick_time
                    elif (i == 2) : state_time = self.cornerkick_time
                    elif (i == 3) : state_time = self.penaltykick_time
                    if (((self.game_state != i+1) and (self.game_state != 0)) or (self.time - state_time > period[i])):
                        self.state_view[i] = 0

            do = True
            if ((self.pre_state_view[0] == 0) and (self.state_view[0] == 1)):
                num = 4
                ori = orientation[num]
                pos = position[num]
            elif ((self.pre_state_view[1] == 0) and (self.state_view[1] == 1)):
                num = 1 if x > 0 else 3
                ori = orientation[num]
                pos = position[num]
                pn.getField('follow').setSFString("")
            elif (self.state_view[3] == 1):
                t = min(self.time - self.penaltykick_time, 600)
                t = t/600
                if self.half_passed:
                    f = -1 if x > 0 else 1
                else:
                    f = -1 if x < 0 else 1
                ori = [0 - 0.27*t, (-1 + 0.08*t)*f, (0 - 0.27*t)*f, 1.57+0.08*t]
                pos = [-0.89*f, (0.5+2.7*t) * sc, 0]
                pn.getField('follow').setSFString("")
            elif ((sum(self.pre_state_view) == 1) and (sum(self.state_view) == 0)):
                num = 0
                ori = orientation[num]
                pos = position[num]
                pn.getField('follow').setSFString("soccer_ball")
            else:
                do = False

            if do:
                pn.getField('orientation').setSFRotation(ori)
                pn.getField('position').setSFVec3f(pos)
            else:
                if ((sum(self.pre_state_view) == 0) and (sum(self.state_view) == 0)):
                    cur_view = pn.getField('position').getSFVec3f()
                    if self.time%15000 < 11000:
                        dx = abs(cur_view[0] - f*x)
                        dy = abs(cur_view[2] - (5.86 * sc - f*y))
                        if dx > 2:
                            pn.getField('orientation').setSFRotation(orientation[0])
                            pn.getField('position').setSFVec3f([f * x, 5.27 * sc, cur_view[2]])
                        if dy > 1.5:
                            pn.getField('orientation').setSFRotation(orientation[0])
                            pn.getField('position').setSFVec3f([cur_view[0], 5.27 * sc, 5.86 * sc - f * y])
                    elif self.time%15000 == 11000:
                        pn.getField('orientation').setSFRotation(orientation[0])
                        pn.getField('position').setSFVec3f([f * x, 2.3 * sc, 2.7 * sc - f * y])
                    elif self.time%15000 < 15000:
                        dx = abs(cur_view[0] - f*x)
                        dy = abs(cur_view[2] - (2.7 * sc - f*y))
                        if dx > 1.5:
                            pn.getField('orientation').setSFRotation(orientation[0])
                            pn.getField('position').setSFVec3f([f * x, 2.3 * sc, cur_view[2]])
                        if dy > 1.2:
                            pn.getField('orientation').setSFRotation(orientation[0])
                            pn.getField('position').setSFVec3f([cur_view[0], 2.3 * sc, 2.7 * sc - f * y])
                    elif self.time%15000 == 0:
                        pn.getField('orientation').setSFRotation(orientation[0])
                        pn.getField('position').setSFVec3f([f * x, 5.27 * sc, 5.86 * sc - f * y])

            for i in range(4):
                self.pre_state_view[i] = self.state_view[i]

    def score_view(self, state):
        if self.multi_view:
            pn = self.getFromDef("DEF_AUDVIEW")
            x = self.get_ball_position()[0]
            sc = 1 if self.type == 0 else 1.3
            if self.half_passed:
                t = 0 if x < 0 else 1
            else:
                t = 0 if x > 0 else 1

            ori = [ [   [-0.072, -1.000, -0.170,  2.352],
                        [-0.390, -0.910, -0.150,  0.870]    ],
                    [   [-0.390,  0.910,  0.150,  0.870],
                        [-0.072,  1.000,  0.170,  2.352]    ]
            ]
            pos = [ [   [ 2.00 * sc,  0.95 * sc, -1.60 * sc],
                        [ 2.00 * sc,  0.95 * sc,  1.60 * sc]   ],
                    [   [-2.00 * sc,  0.95 * sc,  1.60 * sc],
                        [-2.00 * sc,  0.95 * sc, -1.60 * sc]   ]
            ]

            pn.getField('orientation').setSFRotation(ori[t][state])
            pn.getField('position').setSFVec3f(pos[t][state])

    def start_view(self):
        pn = self.getFromDef("DEF_AUDVIEW")
        sc = 1 if self.type == 0 else 1.3

        for t in range(50):
            if self.multi_view:
                ori = [-1.00,  0.00,  0.00,  0.76]
                pos = [0, (42.27 - 37*t/40) * sc, (44.86 - 39*t/40) * sc]
                if t > 40:
                    pos = [0, 5.27 * sc, 5.86 * sc]

                pn.getField('orientation').setSFRotation(ori)
                pn.getField('position').setSFVec3f(pos)

            if self.step(40) == -1:
                break

    ## speaker ##
    def kick_sound(self, touch):
        if sum(touch[0])+sum(touch[1]) != 0:
            if self.time - self.kick_sound_filter >= 400:
                self.kick_sound_filter = self.time
                self.sound_speaker(self.constants.KICK_SOUND)

    def sound_speaker(self, state):
        sounds = ["sounds/kick.wav",
                "sounds/whistle.wav",
                "sounds/whistle_long.wav",
                "sounds/whistle_2.wav",
                "sounds/whistle_3.wav",
                "sounds/goal.wav"
        ]
                    # left, right, sound, volume, pitch, balance, loop
        Speaker.playSound(self.speaker, self.speaker, sounds[state], 1, 1, 0, False)

    def background_music(self, play_stop):
        if play_stop:
            Speaker.playSound(self.speaker, self.speaker, "sounds/crowd.wav", 1, 1, 0, True)
        else:
            Speaker.stop(self.speaker, "sounds/crowd.wav")

    ## keyboard ##
    def overhead_patch(self, team):
        for id in range(self.constants.NUMBER_OF_ROBOTS):
            robot = self.getFromDef(get_robot_name(self, team, id))
            patches = robot.getField('patches')
            number = patches.getMFNode(0)
            number.getField('overheadpatch').setSFBool(self.keyboard[team])

    def light_control(self, team, num):
        for id in range(self.constants.NUMBER_OF_ROBOTS):
            robot = self.robot[team][id]['node']
            if id == int(num):
                slc = [1,1,0]
            else:
                slc = [0,0,0]
            robot.getField('slc').setSFColor(slc)

    def keyboard_light_patch(self):
        for team in self.constants.TEAMS:
            if not self.keyboard[team]:
                for id in range(self.constants.NUMBER_OF_ROBOTS):
                    robot = self.robot[team][id]['node']
                    robot.getField('slc').setSFColor([0,0,0])
            self.overhead_patch(team)

    ## replay ##
    def rewind_robots(self):
        n = 3 if self.multi_view else 1
        for j in range(n):
            for i in range(len(self.replayBuffer)):
                robot_data = self.replayBuffer[i][0]
                for team in self.constants.TEAMS:
                    for id in range(self.constants.NUMBER_OF_ROBOTS):
                        robot = self.robot[team][id]['node']
                        translation = robot_data[team][id]['translation']
                        rotation = robot_data[team][id]['rotation']
                        custom_data = robot_data[team][id]['customData']
                        lwTranslation = robot_data[team][id]['lwTranslation']
                        lwRotation = robot_data[team][id]['lwRotation']
                        rwTranslation = robot_data[team][id]['rwTranslation']
                        rwRotation = robot_data[team][id]['rwRotation']
                        velocity = robot_data[team][id]['velocity']
                        fsTranslation = robot_data[team][id]['fsTranslation']
                        fsRotation = robot_data[team][id]['fsRotation']
                        if id == 0:
                            bbsTranslation = robot_data[team][id]['bbsTranslation']
                            rbsTranslation = robot_data[team][id]['rbsTranslation']
                            lbsTranslation = robot_data[team][id]['lbsTranslation']
                        bsTranslation = robot_data[team][id]['bsTranslation']
                        bsRotation = robot_data[team][id]['bsRotation']
                        laTranslation = robot_data[team][id]['laTranslation']
                        raTranslation = robot_data[team][id]['raTranslation']
                        laRotation = robot_data[team][id]['laRotation']
                        raRotation = robot_data[team][id]['raRotation']
                        llTranslation = robot_data[team][id]['llTranslation']
                        rlTranslation = robot_data[team][id]['rlTranslation']
                        llRotation = robot_data[team][id]['llRotation']
                        rlRotation = robot_data[team][id]['rlRotation']
                        if self.type == 1:
                            llTranslation2 = robot_data[team][id]['llTranslation2']
                            rlTranslation2 = robot_data[team][id]['rlTranslation2']
                            llRotation2 = robot_data[team][id]['llRotation2']
                            rlRotation2 = robot_data[team][id]['rlRotation2']
                        robot.getField('translation').setSFVec3f(translation)
                        robot.getField('rotation').setSFRotation(rotation)
                        robot.getField('customData').setSFString(custom_data)
                        robot.getField('lwTranslation').setSFVec3f(lwTranslation)
                        robot.getField('lwRotation').setSFRotation(lwRotation)
                        robot.getField('rwTranslation').setSFVec3f(rwTranslation)
                        robot.getField('rwRotation').setSFRotation(rwRotation)
                        robot.setVelocity(velocity)
                        robot.getField('fsTranslation').setSFVec3f(fsTranslation)
                        robot.getField('fsRotation').setSFRotation(fsRotation)
                        if id == 0:
                            robot.getField('bbsTranslation').setSFVec3f(bbsTranslation)
                            robot.getField('rbsTranslation').setSFVec3f(rbsTranslation)
                            robot.getField('lbsTranslation').setSFVec3f(lbsTranslation)
                        robot.getField('bsTranslation').setSFVec3f(bsTranslation)
                        robot.getField('bsRotation').setSFRotation(bsRotation)
                        robot.getField('laTranslation').setSFVec3f(laTranslation)
                        robot.getField('raTranslation').setSFVec3f(raTranslation)
                        robot.getField('laRotation').setSFRotation(laRotation)
                        robot.getField('raRotation').setSFRotation(raRotation)
                        robot.getField('llTranslation').setSFVec3f(llTranslation)
                        robot.getField('rlTranslation').setSFVec3f(rlTranslation)
                        robot.getField('llRotation').setSFRotation(llRotation)
                        robot.getField('rlRotation').setSFRotation(rlRotation)
                        if self.type == 1:
                            robot.getField('llTranslation2').setSFVec3f(llTranslation2)
                            robot.getField('rlTranslation2').setSFVec3f(rlTranslation2)
                            robot.getField('llRotation2').setSFRotation(llRotation2)
                            robot.getField('rlRotation2').setSFRotation(rlRotation2)
                        robot.resetPhysics()

                ball_data = self.replayBuffer[i][1]
                translation = ball_data['translation']
                rotation = ball_data['rotation']
                velocity = ball_data['velocity']
                ball = self.ball
                ball.getField('translation').setSFVec3f(translation)
                ball.getField('rotation').setSFRotation(rotation)
                ball.setVelocity(velocity)
                ball.resetPhysics()

                _ = self.get_robot_touch_ball()
                if abs(translation[0]) > self.constants.FIELD_LENGTH / 2 and abs(translation[2]) < self.constants.GOAL_WIDTH / 2 and abs(translation[1]) < 0.33:
                    pre_ball_data = self.replayBuffer[i-1][1]
                    pre_translation = pre_ball_data['translation']
                    if abs(pre_translation[0]) < self.constants.FIELD_LENGTH/2:
                        self.sound_speaker(self.constants.GOAL_SOUND)
                        self.sound_speaker(self.constants.WHISTLE_SOUND)

                if self.multi_view:
                    x = translation[0]
                    y = translation[2]
                    sc = 1 if self.type == 0 else 1.3
                    last_ball = self.replayBuffer[-1][1]
                    translation = last_ball['translation']
                    rl = -1 if translation[0] < 0 else 1
                    pn = self.getFromDef("DEF_AUDVIEW")
                    if j == 0:
                        pn.getField('orientation').setSFRotation([-1.00, 0.00, 0.00, 0.76])
                        pn.getField('position').setSFVec3f([x, 5.27 * sc, 5.86 * sc + y])
                    elif j == 1:
                        pn.getField('orientation').setSFRotation([-0.3, -rl * 0.9, -rl * 0.3, 1.67])
                        pn.getField('position').setSFVec3f([x - rl * 3 * sc, 2.6 * sc, y])
                    else:
                        if x*rl <= 0:
                            a, b, c = 0.97, 0.172, 1.6
                        elif abs(x) > 4:
                            a, b, c = 0.92, 0.277, 1.655
                        else:
                            a = 0.97 - abs(x)*5/4 * 0.01
                            b = math.sqrt((1-a*a)/2)
                            c = 1.6 + abs(x)*5/4 * 0.011
                        pn.getField('orientation').setSFRotation([-b, rl * a, rl * b, c])
                        pn.getField('position').setSFVec3f([rl * 6.5 * sc, 2.47 * sc, y])
                    pn.getField('follow').setSFString("")

                self.ball_spotlight()

                if i%10 < 7:
                    self.setLabel(99, 'REPLAY', 0.7, 0.05, 0.15, 0xcc0000, 0, 'Impact')
                else:
                    self.setLabel(99, '', 0.7, 0.05, 0.15, 0x00000000, 0, 'Arial')

                if self.step(self.timeStep) == -1:
                    break

        self.setLabel(99, '', 0.7, 0.05, 0.15, 0x00000000, 0, 'Arial')

    def update_replayBuffer(self):
        robot_data = [[0 for x in range(self.constants.NUMBER_OF_ROBOTS)] for y in range(2)]
        ball_data = {}
        for team in self.constants.TEAMS:
            for id in range(self.constants.NUMBER_OF_ROBOTS):
                robot = self.robot[team][id]['node']
                ball = self.ball         
                robot_data[team][id] = {}
                robot_data[team][id]['translation'] = robot.getField('translation').getSFVec3f()
                robot_data[team][id]['rotation'] = robot.getField('rotation').getSFRotation()
                robot_data[team][id]['customData'] = robot.getField('customData').getSFString()
                robot_data[team][id]['lwTranslation'] = robot.getField('lwTranslation').getSFVec3f()
                robot_data[team][id]['lwRotation'] = robot.getField('lwRotation').getSFRotation()
                robot_data[team][id]['rwTranslation'] = robot.getField('rwTranslation').getSFVec3f()
                robot_data[team][id]['rwRotation'] = robot.getField('rwRotation').getSFRotation()
                robot_data[team][id]['velocity'] = robot.getVelocity()
                robot_data[team][id]['fsTranslation'] = robot.getField('fsTranslation').getSFVec3f()
                robot_data[team][id]['fsRotation'] = robot.getField('fsRotation').getSFRotation()
                if id == 0:
                    robot_data[team][id]['bbsTranslation'] = robot.getField('bbsTranslation').getSFVec3f()
                    robot_data[team][id]['rbsTranslation'] = robot.getField('rbsTranslation').getSFVec3f()
                    robot_data[team][id]['lbsTranslation'] = robot.getField('lbsTranslation').getSFVec3f()
                robot_data[team][id]['bsTranslation'] = robot.getField('bsTranslation').getSFVec3f()
                robot_data[team][id]['bsRotation'] = robot.getField('bsRotation').getSFRotation()
                robot_data[team][id]['laTranslation'] = robot.getField('laTranslation').getSFVec3f()
                robot_data[team][id]['raTranslation'] = robot.getField('raTranslation').getSFVec3f()
                robot_data[team][id]['laRotation'] = robot.getField('laRotation').getSFRotation()
                robot_data[team][id]['raRotation'] = robot.getField('raRotation').getSFRotation()
                robot_data[team][id]['llTranslation'] = robot.getField('llTranslation').getSFVec3f()
                robot_data[team][id]['rlTranslation'] = robot.getField('rlTranslation').getSFVec3f()
                robot_data[team][id]['llRotation'] = robot.getField('llRotation').getSFRotation()
                robot_data[team][id]['rlRotation'] = robot.getField('rlRotation').getSFRotation()
                if self.type == 1:
                    robot_data[team][id]['llTranslation2'] = robot.getField('llTranslation2').getSFVec3f()
                    robot_data[team][id]['rlTranslation2'] = robot.getField('rlTranslation2').getSFVec3f()
                    robot_data[team][id]['llRotation2'] = robot.getField('llRotation2').getSFRotation()
                    robot_data[team][id]['rlRotation2'] = robot.getField('rlRotation2').getSFRotation()
        ball_data['translation'] = ball.getField('translation').getSFVec3f()
        ball_data['rotation'] = ball.getField('rotation').getSFRotation()
        ball_data['velocity'] = ball.getVelocity()

        self.replayBuffer.append([robot_data, ball_data])

    def init_replayBuffer(self):
        # replay buffer
        self.replay_length = int(self.constants.REPLAY_THRESHOLD / self.constants.PERIOD_MS)
        self.replayBuffer = collections.deque(maxlen=self.replay_length)

    ## spotlight
    def ball_spotlight_stop(self):
        self.spotlight.setVelocity([0, 0, 0, 0, 0, 0])

    def ball_spotlight(self):
        p = self.ball.getPosition()
        v = self.ball.getVelocity()
        self.spotlight.getField('translation').setSFVec3f([p[0], 0.95 + (p[1]-0.05)*2/7, p[2]])
        self.spotlight.setVelocity([v[0], v[1]*2/7, v[2], 0, 0, 0])

    ## license
    def invalid_license(self):
        self.robot = [[0 for _ in range(self.constants.NUMBER_OF_ROBOTS)] for _ in range(2)]
        for _ in range(2):
            for t in self.constants.TEAMS:
                for id in range(self.constants.NUMBER_OF_ROBOTS):
                    node = self.getFromDef(get_robot_name(self, t, id))
                    self.robot[t][id] = {}
                    self.robot[t][id]['node'] = node
                    self.robot[t][id]['active'] = True
                    custom_0 = '0 0 0 0 0 0 0 0' if self.type == 1 else '0 0 0 0 0'
                    node.getField('customData').setSFString(custom_0)
                    self.relocate_all(t, id)
                for i in range(0, self.timeStep, self.basicTimeStep):
                    if Supervisor.step(self, self.basicTimeStep) == -1:
                        break
        self.setLabel(96, 'There is a problem with your license.', 0.15, 0.80, 0.1, 0x000000, 0, 'Tahoma')
        self.setLabel(97, 'Please check license information.', 0.15, 0.84, 0.1, 0x000000, 0, 'Tahoma')
        self.setLabel(98, 'Send your email and your mac address.', 0.15, 0.88, 0.1, 0x000000, 0, 'Tahoma')
        self.setLabel(99, 'Your mac address is \"'+getmac.get_mac_address()+'\".', 0.15, 0.92, 0.1, 0x000000, 0, 'Tahoma')

    ## dribble
    def ball_in_dribble_area(self, team, id):
        ball_x = self.get_ball_position()[0]
        ball_y = self.get_ball_position()[1]
        ball_z = self.get_ball_position()[2]
        robot_pos = self.get_robot_posture(team, id)
        x = robot_pos[0]
        y = robot_pos[1]
        z = robot_pos[2]
        th = robot_pos[3]
        #robot pos and ball pos received

        theta = th
        if (th > self.constants.PI):
            theta -= 2*self.constants.PI
        d_theta = abs(theta - math.atan2(ball_y-y, ball_x-x))
        if (d_theta > self.constants.PI):
            d_theta -= 2*self.constants.PI
        dist = math.sqrt((ball_y - y)*(ball_y - y)+(ball_x - x)*(ball_x - x))
        speed_m = (abs(self.speeds_buffer[team][6*id])+abs(self.speeds_buffer[team][6*id+1]))/2
        add = 0
        if (speed_m < 0.5):
            add = 0.5 * 0.11
        else:
            add = speed_m * 0.11
        d_range = self.constants.ROBOT_SIZE[id]/2 + self.constants.BALL_RADIUS + add

        if ((dist < d_range) and (abs(d_theta) < self.constants.PI/4) and (abs(z - ball_z) < 0.01)):
            return True
        else:
            return False

    def is_kicking(self, team, id):
        return self.fslider_trig[team][id] == 1

    def check_dribble(self):
        # to add:
        # when ball moves quick enough to escape dribble area before next supervisor step
        # lose the ball when the robot rotates fast
        # must be able to head the ball. - by not jumping? how about robot height?
        #

        # roll the ball

        if self.game_state != Game.STATE_DEFAULT:
            self.dribbler = None
            return False

        # start dribble when the robot touches the ball

        # if two or more robot are next to the ball,
        # the dribbler loses the ball (tackled)
        for team in self.constants.TEAMS:
            for id in range(self.constants.NUMBER_OF_ROBOTS):
                robot_pos = self.get_robot_posture(team, id)
                if (team == 0 and robot_pos[0] > 3 and abs(robot_pos[1]) < 0.9) or \
                    (team == 1 and robot_pos[0] < -3 and abs(robot_pos[1]) < 0.9):
                    self.dribbler = None
                    return False
                if self.ball_in_dribble_area(team, id) and self.recent_touch[team][id]:
                    if self.speeds_buffer[team][6*id+5] == 0:
                        self.dribbler = None
                        continue
                    if self.dribbler == None:
                        self.dribbler = (team, id, 0)
                        self.ball_possession[team][id] = True
                        continue
                    if self.dribbler[:2] == (team, id):
                        continue
                    if self.is_kicking(self.dribbler[0], self.dribbler[1]):
                        break
                    else:
                        self.dribbler = None
                        return False

        if self.dribbler != None and self.fslider_trig[self.dribbler[0]][self.dribbler[1]] == 1:
            self.dribbler = None
            return False

        if self.dribbler == None:
            return False

        if self.dribbler != None:
            # if the robot is fallen, not dribbling
            is_dribbling =  self.get_robot_posture(self.dribbler[0], self.dribbler[1])[4] == False

            #if dribbler jumps, he loses the ball
            is_dribbling = is_dribbling or ((self.bslider_count[team][id] < 10) and (self.bslider_count[team][id] != 0))

            if is_dribbling:
                self.dribbler = None
                return False

        return self.dribbler != None

    def dribble_ball(self):
        team, id, f_dribbled = self.dribbler
        robot_pos = self.get_robot_posture(team, id)
        x = robot_pos[0]
        y = robot_pos[1]
        th = robot_pos[3]
        speed_m = (abs(self.speeds_buffer[team][6*id])+abs(self.speeds_buffer[team][6*id+1]))/2
        add = 0.04
        d_range = self.constants.ROBOT_SIZE[id]/2 + self.constants.BALL_RADIUS + add

        t_x = x + d_range*math.cos(th)
        t_y = y + d_range*math.sin(th)
        ball_new = [t_x, t_y]
        r = 1.5 * self.constants.BALL_RADIUS

        node = self.ball
        node.resetPhysics()
        f = -1 if self.half_passed else 1
        translation = [f * ball_new[0], 0.05, -f * ball_new[1]]
        node.getField('translation').setSFVec3f(translation)

        robot_v = self.robot[team][id]['node'].getVelocity()

        ball_rot = [0, 0, 0, 0]
        ball_rot_angle = 0

        ball_lin_v = robot_v[:3]
        axis = np.cross(ball_lin_v, [0, 1, 0])
        if sum(axis) != 0:
            axis = axis / np.linalg.norm(axis)

            if f_dribbled != 0:
                w = np.linalg.norm(ball_lin_v) / self.constants.BALL_RADIUS
                ball_rot_angle = -(f_dribbled * w * self.constants.PERIOD_MS / 1000) % (2 * self.constants.PI)
                
            ball_rot[0] = axis[0]
            ball_rot[1] = axis[1]
            ball_rot[2] = axis[2]
            ball_rot[3] = ball_rot_angle


            self.ball.getField('rotation').setSFRotation(ball_rot)
        ball_velocity = [robot_v[0], robot_v[1], robot_v[2], 0, 0, 0]

        node.setVelocity(ball_velocity)
        self.dribbler = (self.dribbler[0], self.dribbler[1], self.dribbler[2] + 1)

    def dribble(self):
        if self.check_dribble():
            self.dribble_ball()

    def run(self):
        config_file = open('../../config.json')
        config = json.loads(config_file.read())
        self.game_time = self.constants.DEFAULT_GAME_TIME_MS / self.constants.PERIOD_MS * self.constants.PERIOD_MS
        deadlock_flag = True

        license = True
        if config['license']:
            if config['license']['email']:
                email = config['license']['email']
            if config['license']['signature']:
                signature = config['license']['signature']
            else:
                license = False

        if config['rule']:
            if config['rule']['game_time']:
                self.game_time = config['rule']['game_time'] * 1000 / self.constants.PERIOD_MS * self.constants.PERIOD_MS
                self.add_seconds = self.game_time / 1000.0
                self.add_minutes = self.add_seconds // 60
                self.add_seconds -= self.add_minutes * 60
            if not config['rule']['deadlock']:
                deadlock_flag = config['rule']['deadlock']
        else:
            print('"rule" section of \'config.json\' seems to be missing: using default options\n')
        print('Rules:\n')
        print('     game duration - ' + str(self.game_time / 1000) + ' seconds\n')
        print('          deadlock - ' + str(deadlock_flag) + '\n')

        # gets other options from 'config.json' (if no option is specified, default option is given)
        # automatic recording of the game (default: false)
        # automatic repetition of the game (default: false)
        player_infos = []
        repeat = False
        record = False
        record_path = ''
        replay = False
        if config['tool']:
            if config['tool']['repeat']:
                repeat = config['tool']['repeat']
            if config['tool']['multi_view']:
                self.multi_view = config['tool']['multi_view']
            if repeat:  # if repeat is enabled, record is forced to be disabled
                print('Game repetition is enabled that the game recording will be disabled.\n')
            elif config['tool']['record']:
                record = config['tool']['record']
            if config['tool']['record_path']:
                record_path = config['tool']['record_path']
            if config['tool']['replay']:
                replay = config['tool']['replay']

        if not self.multi_view:
            pn = self.getFromDef("DEF_AUDVIEW")
            pn.getField('follow').setSFString("")

        path_prefix = '../../'
        team_name = {}
        self.role_info = {}
        self.role_client = {}
        self.ready = [False] * 4  # TEAM_RED, TEAM_BLUE, COMMENTATOR, REPORTER

        # gets the teams' information from 'config.json'
        for team in self.constants.TEAMS:
            if team == self.constants.TEAM_RED:
                tc = 'team_a'
                tc_op = 'team_b'
            else:
                tc = 'team_b'
                tc_op = 'team_a'
            # my team
            name = ''
            rating = 0  # rating is disabled
            exe = ''
            data = ''
            keyboard = False
            if config[tc]:
                if config[tc]['name']:
                    name = config[tc]['name']
                if config[tc]['executable']:
                    exe = config[tc]['executable']
                if config[tc]['datapath']:
                    data = config[tc]['datapath']
                if config[tc]['keyboard']:
                    keyboard = config[tc]['keyboard']
            self.keyboard[team] = keyboard
            # opponent
            name_op = ''
            rating_op = 0  # rating is disabled
            if config[tc_op]:
                if config[tc_op]['name']:
                    name_op = config[tc_op]['name']
            player_infos.append({
                'name': name,
                'rating': rating,
                'exe': path_prefix + exe,
                'path_prefix': path_prefix + data,
                'role': team
            })

            if team == self.constants.TEAM_RED:
                print('Team A:\n')
            else:
                print('Team B:\n')
            print('  team name - ' + name + '\n')
            team_name[team] = name
            print('  executable - ' + exe + '\n')
            print('  data path - ' + data + '\n\n')
            print('  keyboard - ' + str(keyboard) + '\n\n')

            # create information for aiwc.get_info() in advance
            info = {}
            info['field'] = [self.constants.FIELD_LENGTH, self.constants.FIELD_WIDTH]
            info['goal'] = [self.constants.GOAL_DEPTH, self.constants.GOAL_WIDTH]
            info['penalty_area'] = [self.constants.PENALTY_AREA_DEPTH, self.constants.PENALTY_AREA_WIDTH]
            info['goal_area'] = [self.constants.GOAL_AREA_DEPTH, self.constants.GOAL_AREA_WIDTH]
            info['ball_radius'] = self.constants.BALL_RADIUS
            info['ball_mass'] = self.constants.BALL_MASS
            info['robot_size'] = self.constants.ROBOT_SIZE
            info['robot_height'] = self.constants.ROBOT_HEIGHT
            info['axle_length'] = self.constants.AXLE_LENGTH
            info['robot_body_mass'] = self.constants.ROBOT_BODY_MASS
            info['wheel_radius'] = self.constants.WHEEL_RADIUS
            info['wheel_mass'] = self.constants.WHEEL_MASS
            info['sliders_mass'] = self.constants.SLIDERS_MASS
            info['max_linear_velocity'] = self.constants.MAX_LINEAR_VELOCITY
            info['max_torque'] = self.constants.MAX_TORQUE
            info['resolution'] = [self.constants.RESOLUTION_X, self.constants.RESOLUTION_Y]
            info['number_of_robots'] = self.constants.NUMBER_OF_ROBOTS
            info['codewords'] = self.constants.CODEWORDS
            info['game_time'] = self.game_time / 1000
            info['team_info'] = [[['name_a', name], ['rating', rating]], [['name_b', name_op], ['rating', rating_op]]]
            info['key'] = random_string(self.constants.KEY_LENGTH)
            info['keyboard'] = keyboard
            self.role_info[team] = info

        # gets commentator information from 'config.json' (commentator is optional)
        if config['commentator']:
            name = ''
            exe = ''
            data = ''

            info = {}
            if config['commentator']['name']:
                name = config['commentator']['name']
            if config['commentator']['executable']:
                exe = config['commentator']['executable']
            if config['commentator']['datapath']:
                data = config['commentator']['datapath']
            if exe:
                player_infos.append({
                    'name': name,
                    'rating': 0,
                    'exe': path_prefix + exe,
                    'path_prefix': path_prefix + data,
                    'role': self.constants.COMMENTATOR
                })
                print('Commentator:\n')
                print('  team name - ' + name + '\n')
                print('  executable - ' + exe + '\n')
                print('  data path - ' + data + '\n\n')
                info['key'] = random_string(self.constants.KEY_LENGTH)
            else:
                print('Commentator "executable" is missing: skipping commentator\n')
                self.ready[self.constants.COMMENTATOR] = True

            self.role_info[self.constants.COMMENTATOR] = info
        else:
            print('"commentator" section of \'config.json\' seems to be missing: skipping commentator\n')

        #  gets reporter information from 'config.json' (reporter is optional)
        if config['reporter']:
            exe = ''
            data = ''

            info = {}
            if config['reporter']['name']:
                info['name'] = config['reporter']['name']
            if config['reporter']['executable']:
                exe = config['reporter']['executable']
            if config['reporter']['datapath']:
                data = config['reporter']['datapath']
            if exe:
                player_infos.append({
                    'name': name,
                    'rating': 0,
                    'exe': path_prefix + exe,
                    'path_prefix': path_prefix + data,
                    'role': self.constants.REPORTER
                })
                print('Reporter:\n')
                print('  team name - ' + info['name'] + '\n')
                print('  executable - ' + exe + '\n')
                print('  data path - ' + data + '\n\n')
                info['key'] = random_string(self.constants.KEY_LENGTH)
            else:
                print('Reporter "executable" is missing: skipping reporter\n')
                self.ready[self.constants.REPORTER] = True

            self.role_info[self.constants.REPORTER] = info
        else:
            print('"reporter" section of \'config.json\' seems to be missing: skipping reporter\n')

        self.tcp_server = TcpServer(self.constants.SERVER_IP, self.constants.SERVER_PORT)
        self.ball = self.getFromDef(self.constants.DEF_BALL)
        self.time = 0
        self.kick_sound_filter = 0
        self.kickoff_time = self.time
        self.score = [0, 0]
        self.half_passed = False
        self.reset_reason = Game.NONE
        self.game_state = Game.STATE_KICKOFF
        self.ball_ownership = self.constants.TEAM_RED  # red
        self.robot = [[0 for x in range(self.constants.NUMBER_OF_ROBOTS)] for y in range(2)]
        for t in self.constants.TEAMS:
            for id in range(self.constants.NUMBER_OF_ROBOTS):
                node = self.getFromDef(get_robot_name(self, t, id))
                self.robot[t][id] = {}
                self.robot[t][id]['node'] = node
                self.robot[t][id]['active'] = True
                self.robot[t][id]['touch'] = False
                self.robot[t][id]['ball_possession'] = False
                self.robot[t][id]['niopa_time'] = self.time  # not_in_opponent_penalty_area time
                self.robot[t][id]['ipa_time'] = self.time  # goalkeeper in_penalty_area time
        self.reset(self.constants.FORMATION_KICKOFF, self.constants.FORMATION_DEFAULT)
        self.lock_all_robots(True)
        self.robot[self.constants.TEAM_RED][4]['active'] = True

        if replay:
            # initiate replayBuffer used to replay score situations
            self.init_replayBuffer()

        self.keyboard_light_patch()

        # start participants
        for player_info in player_infos:
            exe = player_info['exe']
            if not os.path.exists(exe):
                print('Participant controller not found: ' + exe)
            else:
                command_line = []
                if exe.endswith('.py'):
                    os.environ['PYTHONPATH'] += os.pathsep + os.path.join(os.getcwd(), 'player_py')
                    if sys.platform == 'win32':
                        command_line.append('python')
                command_line.append(exe)
                command_line.append(self.constants.SERVER_IP)
                command_line.append(str(self.constants.SERVER_PORT))
                command_line.append(self.role_info[player_info['role']]['key'])
                command_line.append(player_info['path_prefix'])
                print(command_line)
                subprocess.Popen(command_line)
        self.started = False
        print('Waiting for player to be ready...')

        while True:
            sys.stdout.flush()
            self.tcp_server.spin(self)
            if not self.started:
                if all(self.ready):
                    if record:
                        print('Game recording is enabled.')
                        time_info = time.localtime()
                        record_fullpath = '{}/[{:04d}-{:02d}-{:02d}T{:02d}_{:02d}_{:02d}]{}_{}.mp4'.format(
                            record_path,
                            # [<year>-<month>-<day>T<hour>_<minute>_<seconds>]
                            time_info[0], time_info[1], time_info[2], time_info[3], time_info[4], time_info[5],
                            team_name[self.constants.TEAM_RED], team_name[self.constants.TEAM_BLUE]
                            )
                        self.movieStartRecording(record_fullpath, 1920, 1080, 0, 100, 1, False)
                    print('Starting match.')
                    self.started = True
                    self.ball_position = self.get_ball_position()
                    self.publish_current_frame(Game.GAME_START)
                    if self.step(self.constants.WAIT_STABLE_MS) == -1:
                        break
                    self.start_view()
                    self.sound_speaker(self.constants.WHISTLE_LONG_SOUND)
                    self.background_music(True)
                else:
                    if self.step(self.timeStep) == -1:
                        break
                    else:
                        self.waitReady += self.timeStep
                        if (self.waitReady == self.constants.WAIT_READY_MS):
                            print('Game could not be initiated. Need two players ready.')
                            return
                    ###### try to change
                    self.reset(self.constants.FORMATION_KICKOFF, self.constants.FORMATION_DEFAULT)
                    self.lock_all_robots(True)
                    self.robot[self.constants.TEAM_RED][4]['active'] = True
                continue

            self.ball_position = self.get_ball_position()
            if self.time >= self.game_time:  # half of game over
                if self.half_passed:  # game over
                    self.sound_speaker(self.constants.WHISTLE_3_SOUND)
                    self.background_music(False)
                    if repeat:
                        self.publish_current_frame(Game.EPISODE_END)
                        self.reset_reason = Game.EPISODE_END
                        self.stop_robots()
                        if self.step(self.constants.WAIT_END_MS) == -1:
                            break
                        self.half_passed = False
                        self.episode_restart()
                        self.ball_ownership = self.constants.TEAM_RED
                        self.game_state = Game.STATE_KICKOFF
                        self.time = 0
                        self.kick_sound_filter = 0
                        self.kickoff_time = self.time
                        self.score = [0, 0]
                        self.reset(self.constants.FORMATION_KICKOFF, self.constants.FORMATION_DEFAULT)
                        self.lock_all_robots(True)
                        self.robot[self.constants.TEAM_RED][4]['active'] = True
                        if self.step(self.constants.WAIT_STABLE_MS) == -1:
                            break
                        self.publish_current_frame(Game.GAME_START)
                    else:
                        self.publish_current_frame(Game.GAME_END)
                    self.stop_robots()
                    if self.step(self.constants.WAIT_END_MS) == -1:
                        break
                    self.tcp_server.spin(self)  # leave time to receive report
                    if not repeat:
                        break
                    else:
                        self.sound_speaker(self.constants.WHISTLE_LONG_SOUND)
                        self.background_music(True)
                else:  # second half starts with a kickoff by the blue team (1)
                    self.sound_speaker(self.constants.WHISTLE_2_SOUND)
                    self.publish_current_frame(Game.HALFTIME)
                    self.stop_robots()
                    if self.step(self.constants.WAIT_END_MS) == -1:
                        break
                    self.half_passed = True
                    self.mark_half_passed()
                    self.ball_ownership = self.constants.TEAM_BLUE
                    self.game_state = Game.STATE_KICKOFF
                    self.time = 0
                    self.kst = 0
                    self.kickoff_time = self.time
                    self.reset(self.constants.FORMATION_DEFAULT, self.constants.FORMATION_KICKOFF)
                    self.lock_all_robots(True)
                    self.robot[self.constants.TEAM_BLUE][4]['active'] = True
                    if self.step(self.constants.WAIT_STABLE_MS) == -1:
                        break
                    self.publish_current_frame(Game.GAME_START)
                    self.sound_speaker(self.constants.WHISTLE_LONG_SOUND)
                continue

            self.publish_current_frame()
            self.reset_reason = Game.NONE

            if replay:
                # update robot data
                self.update_replayBuffer()

            # update ball possession statuses of robots
            ball_possession = self.get_ball_possession()
            for team in self.constants.TEAMS:
                for id in range(self.constants.NUMBER_OF_ROBOTS):
                    self.robot[team][id]['ball_possession'] = ball_possession[team][id]
                    if ball_possession[team][id]:
                        self.ball_possession = ball_possession

            # update touch statuses of robots
            touch = self.get_robot_touch_ball()
            for team in self.constants.TEAMS:
                for id in range(self.constants.NUMBER_OF_ROBOTS):
                    self.robot[team][id]['touch'] = touch[team][id]
                    if touch[team][id]:  # if any of the robots has touched the ball at this frame, update touch status
                        self.recent_touch = touch

            # check if any of robots has fallen
            for team in self.constants.TEAMS:
                for id in range(self.constants.NUMBER_OF_ROBOTS):
                    # if a robot has fallen and could not recover for constants.FALL_TIME_MS, send the robot to foulzone
                    if self.robot[team][id]['active'] \
                       and self.time - self.robot[team][id]['fall_time'] >= self.constants.FALL_TIME_MS:
                        self.robot[team][id]['active'] = False
                        self.send_to_foulzone(team, id)
                        self.robot[team][id]['sentout_time'] = self.time
                    elif self.get_robot_posture(team, id)[4]:  # robot is standing properly
                        self.robot[team][id]['fall_time'] = self.time

            self.change_view()
            self.ball_spotlight()
            
            # check if any of robots has been left the field without send_to_foulzone()
            for team in self.constants.TEAMS:
                for id in range(self.constants.NUMBER_OF_ROBOTS):
                    # an active robot is not in the field
                    if self.robot[team][id]['active'] and not self.robot_in_field(team, id):
                        # make the robot inactive and send out
                        self.robot[team][id]['active'] = False
                        self.send_to_foulzone(team, id)
                        self.robot[team][id]['sentout_time'] = self.time

            # check if any of robots are in the opponent's penalty area
            def is_in_opponent_goal(x, y):
                return (x > self.constants.FIELD_LENGTH / 2) and (abs(y) < self.constants.GOAL_WIDTH / 2)

            def is_in_opponent_penalty_area(x, y):
                return (x <= self.constants.FIELD_LENGTH / 2) \
                   and (x > self.constants.FIELD_LENGTH / 2 - self.constants.PENALTY_AREA_DEPTH) \
                   and (abs(y) < self.constants.PENALTY_AREA_WIDTH / 2)

            for team in self.constants.TEAMS:
                for id in range(self.constants.NUMBER_OF_ROBOTS):
                    pos = self.get_robot_posture(team, id)
                    sign = 1 if team == self.constants.TEAM_RED else -1
                    x = sign * pos[0]
                    y = sign * pos[1]
                    # if a robot has been in the opponent's penalty area for more than constants.IOPA_TIME_LIMIT_MS seconds,
                    # the robot is relocated to the initial position
                    if is_in_opponent_goal(x, y) or is_in_opponent_penalty_area(x, y):
                        if self.time - self.robot[team][id]['niopa_time'] >= self.constants.IOPA_TIME_LIMIT_MS:
                            ix = sign * self.constants.ROBOT_FORMATION[self.constants.FORMATION_DEFAULT][id][0]
                            iy = sign * self.constants.ROBOT_FORMATION[self.constants.FORMATION_DEFAULT][id][1]
                            r = 1.5 * self.constants.ROBOT_SIZE[id]
                            # if any object is located within 1.5 * robot_size, the relocation is delayed
                            if not self.any_object_nearby(ix, iy, r):
                                self.return_to_field(team, id)
                                self.robot[team][id]['niopa_time'] = self.time
                    else:
                        self.robot[team][id]['niopa_time'] = self.time

            self.dribble()

            # check if the goalkeeper is in the own penalty area
            def is_in_goal(x, y):
                return (x < -self.constants.FIELD_LENGTH / 2) and (abs(y) < self.constants.GOAL_WIDTH / 2)

            def is_in_penalty_area(x, y):
                return (x >= -self.constants.FIELD_LENGTH / 2) and \
                       (x < -self.constants.FIELD_LENGTH / 2 + self.constants.PENALTY_AREA_DEPTH) and \
                       (abs(y) < self.constants.PENALTY_AREA_WIDTH / 2)

            for team in self.constants.TEAMS:
                pos = self.get_robot_posture(team, 0)
                sign = 1 if team == self.constants.TEAM_RED else -1
                x = sign * pos[0]
                y = sign * pos[1]
                # if the goalkeeper has been not in the penalty area for more than constants.GK_NIPA_TIME_LIMIT_MS seconds,
                # the robot is returned to the initial position
                if is_in_goal(x, y) or is_in_penalty_area(x, y):
                    self.robot[team][0]['ipa_time'] = self.time
                elif self.time - self.robot[team][0]['ipa_time'] >= self.constants.GK_NIPA_TIME_LIMIT_MS:
                    ix = sign * self.constants.ROBOT_FORMATION[self.constants.FORMATION_DEFAULT][0][0]
                    iy = sign * self.constants.ROBOT_FORMATION[self.constants.FORMATION_DEFAULT][0][1]
                    r = 1.5 * self.constants.ROBOT_SIZE[0]
                    # if any object is located within 1.5 * robot_size, the return is delayed
                    if not self.any_object_nearby(ix, iy, r):
                        self.robot[team][0]['active'] = True
                        self.return_to_field(team, 0)
                        self.robot[team][0]['ipa_time'] = self.time
            
            if self.game_state == Game.STATE_DEFAULT:
                ball_x = self.ball_position[0]
                ball_y = self.ball_position[1]
                ball_z = self.ball_position[2]
                if abs(ball_x) > self.constants.FIELD_LENGTH / 2 and abs(ball_y) < self.constants.GOAL_WIDTH / 2 and abs(ball_z) < 0.33:
                    goaler = self.constants.TEAM_RED if ball_x > 0 else self.constants.TEAM_BLUE
                    self.score[goaler] += 1
                    self.update_label()
                    self.stop_robots()
                    self.sound_speaker(self.constants.GOAL_SOUND)
                    self.sound_speaker(self.constants.WHISTLE_SOUND)
                    for i in range(0, self.constants.WAIT_GOAL_MS, self.timeStep):
                        if i == self.constants.WAIT_VIEW_MS:
                            self.score_view(0)
                        elif i == 2*self.constants.WAIT_VIEW_MS:
                            self.score_view(1)
                        if self.step(self.timeStep) == -1:
                            break
                        if replay:
                            # update robot data (after a goal is scored)
                            self.update_replayBuffer()
                        self.ball_spotlight()
                    if replay:
                        # replay loop
                        self.rewind_robots()
                    self.ball_spotlight_stop()
                    self.game_state = Game.STATE_KICKOFF
                    self.ball_ownership = self.constants.TEAM_BLUE if ball_x > 0 else self.constants.TEAM_RED
                    self.kickoff_time = self.time
                    if self.ball_ownership == self.constants.TEAM_RED:
                        self.reset(self.constants.FORMATION_KICKOFF, self.constants.FORMATION_DEFAULT)
                    else:
                        self.reset(self.constants.FORMATION_DEFAULT, self.constants.FORMATION_KICKOFF)
                    self.lock_all_robots(True)
                    self.robot[self.ball_ownership][4]['active'] = True
                    if self.step(self.constants.WAIT_STABLE_MS) == -1:
                        break
                    self.sound_speaker(self.constants.WHISTLE_LONG_SOUND)
                    self.reset_reason = self.constants.SCORE_RED_TEAM if ball_x > 0 else self.constants.SCORE_BLUE_TEAM
                elif not self.ball_in_field():
                    self.ball_spotlight_stop()
                    self.sound_speaker(self.constants.WHISTLE_SOUND)
                    self.stop_robots()
                    if self.step(self.constants.WAIT_STABLE_MS) == -1:
                        break
                    # determine the ownership based on who touched the ball last
                    touch_count = [0, 0]
                    for team in self.constants.TEAMS:
                        for id in range(self.constants.NUMBER_OF_ROBOTS):
                            if self.recent_touch[team][id]:
                                touch_count[team] += 1
                    # if recent_touch_ was red team dominant, blue team gets the ball
                    if touch_count[self.constants.TEAM_RED] > touch_count[self.constants.TEAM_BLUE]:
                        self.ball_ownership = self.constants.TEAM_BLUE
                    elif touch_count[self.constants.TEAM_BLUE] > touch_count[self.constants.TEAM_RED]:  # the other way around
                        self.ball_ownership = self.constants.TEAM_RED
                    else:  # otherwise, the attacking team gets an advantage
                        self.ball_ownership = self.constants.TEAM_BLUE if ball_x < 0 else self.constants.TEAM_RED
                    # happened on the left side
                    if ball_x < 0:  # if the red gets the ball, proceed to goalkick
                        if self.ball_ownership == self.constants.TEAM_RED:
                            self.game_state = Game.STATE_GOALKICK
                            self.goalkick_time = self.time
                            self.reset(self.constants.FORMATION_GOALKICK_A, self.constants.FORMATION_GOALKICK_D)
                            self.lock_all_robots(True)
                            self.robot[self.ball_ownership][0]['active'] = True
                            self.reset_reason = self.constants.GOALKICK
                        else:  # otherwise, proceed to corner kick
                            self.game_state = Game.STATE_CORNERKICK
                            self.cornerkick_time = self.time
                            if ball_y > 0:  # upper left corner
                                self.reset(self.constants.FORMATION_CAD_AD, self.constants.FORMATION_CAD_AA)
                            else:  # lower left corner
                                self.reset(self.constants.FORMATION_CBC_AD, self.constants.FORMATION_CBC_AA)
                            self.lock_all_robots(True)
                            self.robot[self.ball_ownership][4]['active'] = True
                            self.reset_reason = self.constants.CORNERKICK
                    else:  # cornerkick happened on the right side
                        if self.ball_ownership == self.constants.TEAM_BLUE:  # if the blue gets the ball, proceed to goalkick
                            self.game_state = Game.STATE_GOALKICK
                            self.goalkick_time = self.time
                            self.reset(self.constants.FORMATION_GOALKICK_D, self.constants.FORMATION_GOALKICK_A)
                            self.lock_all_robots(True)
                            self.robot[self.ball_ownership][0]['active'] = True
                            self.reset_reason = self.constants.GOALKICK
                        else:  # otherwise, proceed to corenerkick
                            self.game_state = Game.STATE_CORNERKICK
                            self.cornerkick_time = self.time
                            if ball_y > 0:  # upper right corner
                                self.reset(self.constants.FORMATION_CBC_AA, self.constants.FORMATION_CBC_AD)
                            else:  # lower right corner
                                self.reset(self.constants.FORMATION_CAD_AA, self.constants.FORMATION_CAD_AD)
                            self.lock_all_robots(True)
                            self.robot[self.ball_ownership][4]['active'] = True
                            self.reset_reason = self.constants.CORNERKICK
                    if self.step(self.constants.WAIT_STABLE_MS) == -1:
                        break
                    self.sound_speaker(self.constants.WHISTLE_SOUND)

                # check if any of robots should return to the field
                for team in self.constants.TEAMS:
                    for id in range(self.constants.NUMBER_OF_ROBOTS):
                        # sentout time of 0 is an indicator that the robot is currently on the field
                        if self.robot[team][id]['sentout_time'] == 0:
                            continue
                        # if a robot has been sent out and constants.SENTOUT_DURATION_MS has passed,
                        # return the robot back to the field
                        if self.time - self.robot[team][id]['sentout_time'] >= self.constants.SENTOUT_DURATION_MS:
                            # if any object is located within 1.5 * robot_size, the return is delayed
                            s = 1 if team == self.constants.TEAM_RED else -1
                            x = self.constants.ROBOT_FORMATION[self.constants.FORMATION_DEFAULT][id][0] * s
                            y = self.constants.ROBOT_FORMATION[self.constants.FORMATION_DEFAULT][id][1] * s
                            r = 1.5 * self.constants.ROBOT_SIZE[id]
                            if not self.any_object_nearby(x, y, r):
                                self.robot[team][id]['active'] = True
                                self.return_to_field(team, id)
                                self.robot[team][id]['sentout_time'] = 0
                ball_x = self.get_ball_position()[0]
                if self.check_penalty_area():  # if the penalty area reset condition is met
                    # the ball ownership is already set by check_penalty_area()
                    self.sound_speaker(self.constants.WHISTLE_SOUND)
                    self.stop_robots()
                    if self.step(self.constants.WAIT_STABLE_MS) == -1:
                        break
                    if ball_x < 0 and self.ball_ownership == self.constants.TEAM_RED:
                        # proceed to goal kick by Team Red
                        self.game_state = Game.STATE_GOALKICK
                        self.reset_reason = self.constants.GOALKICK
                        self.goalkick_time = self.time
                        self.reset(self.constants.FORMATION_GOALKICK_A, self.constants.FORMATION_GOALKICK_D)
                        self.lock_all_robots(True)
                        self.robot[self.ball_ownership][0]['active'] = True
                    elif ball_x > 0 and self.ball_ownership == self.constants.TEAM_BLUE:
                        # proceed to goal kick by Team Blue
                        self.game_state = Game.STATE_GOALKICK
                        self.reset_reason = self.constants.GOALKICK
                        self.goalkick_time = self.time
                        self.reset(self.constants.FORMATION_GOALKICK_D, self.constants.FORMATION_GOALKICK_A)
                        self.lock_all_robots(True)
                        self.robot[self.ball_ownership][0]['active'] = True
                    elif ball_x < 0 and self.ball_ownership == self.constants.TEAM_BLUE:
                        # proceed to penalty kick by Team Blue
                        self.game_state = Game.STATE_PENALTYKICK
                        self.reset_reason = self.constants.PENALTYKICK
                        self.penaltykick_time = self.time
                        self.reset(self.constants.FORMATION_PENALTYKICK_D, self.constants.FORMATION_PENALTYKICK_A)
                        self.lock_all_robots(True)
                        self.robot[self.ball_ownership][4]['active'] = True
                    else:  # proceed to penalty kick by Team Red
                        self.game_state = Game.STATE_PENALTYKICK
                        self.reset_reason = self.constants.PENALTYKICK
                        self.penaltykick_time = self.time
                        self.reset(self.constants.FORMATION_PENALTYKICK_A, self.constants.FORMATION_PENALTYKICK_D)
                        self.lock_all_robots(True)
                        self.robot[self.ball_ownership][4]['active'] = True
                    if self.step(self.constants.WAIT_STABLE_MS) == -1:
                        break
                    self.sound_speaker(self.constants.WHISTLE_SOUND)

                #for crowdlock
                if self.reset_reason == self.constants.NONE:
                    # calculate dist of the robots
                    dist_count = 0
                    ball_x, ball_y, _ = self.get_ball_position()
                    for team in self.constants.TEAMS:
                        for id in range(self.constants.NUMBER_OF_ROBOTS):
                            robot_pos = self.get_robot_posture(team, id)
                            dist = get_distance(robot_pos[0], robot_pos[1], ball_x, ball_y)
                            if dist <= 0.40:
                                dist_count += 1

                    if dist_count < self.constants.CROWDLOCK_THRESHOLD or self.game_state != Game.STATE_DEFAULT:
                        self.crowdlock_time = self.time
                    elif self.time - self.crowdlock_time >= self.constants.CROWDLOCK_DURATION_MS and self.game_state == Game.STATE_DEFAULT:
                        self.sound_speaker(self.constants.WHISTLE_SOUND)
                        self.stop_robots()
                        if self.step(self.constants.WAIT_STABLE_MS) == -1:
                            break
                        # determine where to relocate and relocate the ball
                        if ball_x < 0:  # Team Red's region
                            if ball_y > 0:  # upper half
                                self.relocate_ball(self.constants.BALL_RELOCATION_A)
                            else:  # lower half
                                self.relocate_ball(self.constants.BALL_RELOCATION_B)
                        else:  # Team Blue's region
                            if ball_y > 0:  # upper half
                                self.relocate_ball(self.constants.BALL_RELOCATION_C)
                            else:  # lower half
                                self.relocate_ball(self.constants.BALL_RELOCATION_D)
                        self.flush_touch_ball()
                        self.relocate_arm_leg_all()
                        if self.step(self.constants.WAIT_STABLE_MS) == -1:
                            break
                        self.reset_reason = self.constants.DEADLOCK
                        self.crowdlock_time = self.time
                        self.sound_speaker(self.constants.WHISTLE_SOUND)

                if self.reset_reason == self.constants.NONE and deadlock_flag:
                    if self.get_ball_velocity() >= self.constants.DEADLOCK_THRESHOLD:
                        self.deadlock_time = self.time

                    elif self.time - self.deadlock_time >= self.constants.DEADLOCK_DURATION_MS:
                        self.sound_speaker(self.constants.WHISTLE_SOUND)
                        # if the ball is not moved fast enough for constants.DEADLOCK_DURATION_MS
                        ball_x = self.get_ball_position()[0]
                        ball_y = self.get_ball_position()[1]
                        # if the deadlock happened in special region
                        if abs(ball_x) > self.constants.FIELD_LENGTH / 2 - self.constants.PENALTY_AREA_DEPTH:
                            # if the deadlock happened inside the penalty area
                            if abs(ball_y) < self.constants.PENALTY_AREA_WIDTH / 2:
                                self.ball_ownership = self.get_pa_ownership()
                                self.stop_robots()
                                if self.step(self.constants.WAIT_STABLE_MS) == -1:
                                    break
                                if ball_x < 0 and self.ball_ownership == self.constants.TEAM_RED:  # proceed to goal kick by Team Red
                                    self.game_state = Game.STATE_GOALKICK
                                    self.reset_reason = self.constants.GOALKICK
                                    self.goalkick_time = self.time
                                    self.reset(self.constants.FORMATION_GOALKICK_A, self.constants.FORMATION_GOALKICK_D)
                                    self.lock_all_robots(True)
                                    self.robot[self.ball_ownership][0]['active'] = True
                                elif ball_x > 0 and self.ball_ownership == self.constants.TEAM_BLUE:
                                    # proceed to goal kick by Team Blue
                                    self.game_state = Game.STATE_GOALKICK
                                    self.reset_reason = self.constants.GOALKICK
                                    self.goalkick_time = self.time
                                    self.reset(self.constants.FORMATION_GOALKICK_D, self.constants.FORMATION_GOALKICK_A)
                                    self.lock_all_robots(True)
                                    self.robot[self.ball_ownership][0]['active'] = True
                                elif ball_x < 0 and self.ball_ownership == self.constants.TEAM_BLUE:
                                    # proceed to penalty kick by Team Blue
                                    self.game_state = Game.STATE_PENALTYKICK
                                    self.reset_reason = self.constants.PENALTYKICK
                                    self.penaltykick_time = self.time
                                    self.reset(self.constants.FORMATION_PENALTYKICK_D, self.constants.FORMATION_PENALTYKICK_A)
                                    self.lock_all_robots(True)
                                    self.robot[self.ball_ownership][4]['active'] = True
                                else:  # proceed to penalty kick by Team Red
                                    self.game_state = Game.STATE_PENALTYKICK
                                    self.reset_reason = self.constants.PENALTYKICK
                                    self.penaltykick_time = self.time
                                    self.reset(self.constants.FORMATION_PENALTYKICK_A, self.constants.FORMATION_PENALTYKICK_D)
                                    self.lock_all_robots(True)
                                    self.robot[self.ball_ownership][4]['active'] = True
                                if self.step(self.constants.WAIT_STABLE_MS) == -1:
                                    break
                                self.sound_speaker(self.constants.WHISTLE_SOUND)
                                self.deadlock_time = self.time

                            else:  # if the deadlock happened in the corner regions
                                # set the ball ownership
                                self.ball_ownership = self.get_corner_ownership()
                                self.stop_robots()
                                if self.step(self.constants.WAIT_STABLE_MS) == -1:
                                    break
                                self.game_state = Game.STATE_CORNERKICK
                                self.cornerkick_time = self.time
                                # determine where to place the robots and the ball
                                if ball_x < 0:  # on Team Red's side
                                    if ball_y > 0:  # on upper side
                                        if self.ball_ownership == self.constants.TEAM_RED:  # ball owned by Team Red
                                            self.reset(self.constants.FORMATION_CAD_DA, self.constants.FORMATION_CAD_DD)
                                        else:  # // ball owned by Team Blue
                                            self.reset(self.constants.FORMATION_CAD_AD, self.constants.FORMATION_CAD_AA)
                                    else:  # on lower side
                                        if self.ball_ownership == self.constants.TEAM_RED:  # ball owned by Team Red
                                            self.reset(self.constants.FORMATION_CBC_DA, self.constants.FORMATION_CBC_DD)
                                        else:  # ball owned by Team Blue
                                            self.reset(self.constants.FORMATION_CBC_AD, self.constants.FORMATION_CBC_AA)
                                else:  # on Team Blue's side
                                    if ball_y > 0:  # on upper side
                                        if self.ball_ownership == self.constants.TEAM_RED:  # ball owned by Team Red
                                            self.reset(self.constants.FORMATION_CBC_AA, self.constants.FORMATION_CBC_AD)
                                        else:  # ball owned by Team Blue
                                            self.reset(self.constants.FORMATION_CBC_DD, self.constants.FORMATION_CBC_DA)
                                    else:  # on lower side
                                        if self.ball_ownership == self.constants.TEAM_RED:  # ball owned by Team Red
                                            self.reset(self.constants.FORMATION_CAD_AA, self.constants.FORMATION_CAD_AD)
                                        else:  # ball owned by Team Blue
                                            self.reset(self.constants.FORMATION_CAD_DD, self.constants.FORMATION_CAD_DA)

                                self.lock_all_robots(True)
                                self.robot[self.ball_ownership][4]['active'] = True
                                if self.step(self.constants.WAIT_STABLE_MS) == -1:
                                    break
                                self.reset_reason = self.constants.CORNERKICK
                                self.deadlock_time = self.time
                                self.sound_speaker(self.constants.WHISTLE_SOUND)

                        else:  # if the deadlock happened in the general region, relocate the ball and continue the game
                            self.stop_robots()
                            if self.step(self.constants.WAIT_STABLE_MS) == -1:
                                break
                            # determine where to relocate and relocate the ball
                            if ball_x < 0:  # Team Red's region
                                if ball_y > 0:  # upper half
                                    self.relocate_ball(self.constants.BALL_RELOCATION_A)
                                else:  # lower half
                                    self.relocate_ball(self.constants.BALL_RELOCATION_B)
                            else:  # Team Blue's region
                                if ball_y > 0:  # upper half
                                    self.relocate_ball(self.constants.BALL_RELOCATION_C)
                                else:  # lower half
                                    self.relocate_ball(self.constants.BALL_RELOCATION_D)
                            self.flush_touch_ball()
                            self.relocate_arm_leg_all()
                            if self.step(self.constants.WAIT_STABLE_MS) == -1:
                                break
                            self.reset_reason = self.constants.DEADLOCK
                            self.deadlock_time = self.time
                            self.sound_speaker(self.constants.WHISTLE_SOUND)

            elif self.game_state == Game.STATE_KICKOFF:
                if self.time - self.kickoff_time >= self.constants.KICKOFF_TIME_LIMIT_MS:
                    self.game_state = Game.STATE_DEFAULT
                    self.lock_all_robots(False)
                else:
                    ball_x = self.ball_position[0]
                    ball_y = self.ball_position[1]
                    if ball_x * ball_x + ball_y * ball_y > self.constants.KICKOFF_BORDER * self.constants.KICKOFF_BORDER:
                        self.game_state = Game.STATE_DEFAULT
                        self.lock_all_robots(False)
                self.deadlock_time = self.time
                if replay:
                    self.init_replayBuffer()

            elif self.game_state == Game.STATE_GOALKICK:
                if self.time - self.goalkick_time >= self.constants.GOALKICK_TIME_LIMIT_MS:  # time limit has passed
                    self.game_state = Game.STATE_DEFAULT
                    self.lock_all_robots(False)
                elif self.robot[self.ball_ownership][0]['touch']:  # the goalie has touched the ball
                    self.game_state = Game.STATE_DEFAULT
                    self.lock_all_robots(False)
                self.deadlock_time = self.time
            elif self.game_state == Game.STATE_CORNERKICK:
                if self.time - self.cornerkick_time >= self.constants.CORNERKICK_TIME_LIMIT_MS:  # time limit has passed
                    self.game_state = Game.STATE_DEFAULT
                    self.lock_all_robots(False)
                else:  # a robot has touched the ball
                    for id in range(self.constants.NUMBER_OF_ROBOTS):
                        if self.robot[self.ball_ownership][id]['touch']:
                            self.game_state = Game.STATE_DEFAULT
                            self.lock_all_robots(False)
                self.deadlock_time = self.time
            elif self.game_state == Game.STATE_PENALTYKICK:
                if self.time - self.penaltykick_time >= self.constants.PENALTYKICK_TIME_LIMIT_MS:  # time limit has passed
                    self.game_state = Game.STATE_DEFAULT
                    self.lock_all_robots(False)
                elif self.robot[self.ball_ownership][4]['touch']:  # the attacker has touched the ball
                    self.game_state = Game.STATE_DEFAULT
                    self.lock_all_robots(False)
                self.deadlock_time = self.time
            if self.step(self.timeStep, runTimer=True) == -1:
                break

        if record:
            # Stop game recording
            print('Saving the recorded game as: {}'.format(record_fullpath))
            print('Please wait until the message \033[36m\"INFO: Video creation finished.\"\033[0m is shown.')
            sys.stdout.flush()
            self.movieStopRecording()

    def save_report(self):
        # Save the report if anything has been written
        if self.report and self.role_info[self.constants.REPORTER]:
            file = open('../../reports/' + self.role_info[self.constants.REPORTER]['name'] + '.txt', 'w')
            file.write(self.report)
            file.close()


controller = GameSupervisor()
controller.run()
controller.save_report()
