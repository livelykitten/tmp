DEF_AUDVIEW = 'DEF_AUDVIEW'
DEF_CAMA = 'DEF_CAMA'
DEF_CAMB = 'DEF_CAMB'
DEF_GRASS = 'DEF_GRASS'
DEF_STADIUM = 'DEF_STADIUM'
DEF_WALL = 'DEF_WALL'
DEF_VISWALL = 'DEF_VISWALL'
NAME_CAMA = 'cam_a'
NAME_CAMB = 'cam_b'
NAME_RECV = 'recv'

# these DEF names are for dynamically created node such as ball and robots
DEF_BALL = 'DEF_BALL'
DEF_BALLSHAPE = 'DEF_BALLSHAPE'
DEF_ORANGESHAPE = 'DEF_ORANGESHAPE'
DEF_ROBOT_PREFIX = 'DEF_ROBOT'

# cams
RESOLUTION_X = 640
RESOLUTION_Y = 480
SUBIMAGE_NX = 40
SUBIMAGE_NY = 40
CAM_PERIOD_MS = 50  # 20 fps = 50 ms
RECV_PERIOD_MS = 50
ESTIMATED_SUBIMAGE_SIZE = (RESOLUTION_X / SUBIMAGE_NX) * (RESOLUTION_Y / SUBIMAGE_NY) * 4 + 100

SCALE = 1.3
#   Field Dimensions
FIELD_LENGTH = 7.8*SCALE
FIELD_WIDTH = 4.65*SCALE
GOAL_DEPTH = 0.45*SCALE
GOAL_WIDTH = 1.0*SCALE
PENALTY_AREA_DEPTH = 0.9*SCALE
PENALTY_AREA_WIDTH = 1.8*SCALE
GOAL_AREA_DEPTH = 0.4*SCALE
GOAL_AREA_WIDTH = SCALE*SCALE
WALL_THICKNESS = 0.025
CORNER_LENGTH = 0.1*SCALE

#   Ball Dimension
BALL_RADIUS = 0.04
BALL_MASS = 0.0184

#  Robot Specifications
NUMBER_OF_ROBOTS = 5
ROBOT_SIZE = [0.15, 0.15, 0.15, 0.15, 0.15]
ROBOT_HEIGHT = [0.42, 0.42, 0.42, 0.42, 0.42]
AXLE_LENGTH = [0.14, 0.14, 0.14, 0.14, 0.14]
ROBOT_BODY_MASS = [2.5, 2.0, 2.0, 1.5, 1.5]
WHEEL_RADIUS = [0.04, 0.04, 0.04, 0.04, 0.04]
WHEEL_MASS = [0.15, 0.10, 0.10, 0.10, 0.10]
SLIDERS_MASS = [2.5, 1.0, 1.0, 1.0, 1.0]
MAX_LINEAR_VELOCITY = [1.8, 2.1, 2.1, 2.55, 2.55]
MAX_TORQUE = [0.8, 1.2, 1.2, 0.4, 0.4]
PI = 3.14159265358979323846
ROBOT_FORMATION = [
  #  x, y, th - Default Formation
  [[-3.8*SCALE,   0.0*SCALE, PI / 2],
   [-2.25*SCALE,  1.0*SCALE, 0],
   [-2.25*SCALE, -1.0*SCALE, 0],
   [-0.65*SCALE,  0.3*SCALE, 0],
   [-0.65*SCALE, -0.3*SCALE, 0]],
  #  x, y, th - Kickoff Formation
  [[-3.8*SCALE,   0.0*SCALE, PI / 2],
   [-2.25*SCALE,  1.0*SCALE, 0],
   [-2.25*SCALE, -1.0*SCALE, 0],
   [-0.9*SCALE,  0.0*SCALE,   0],
   [0.4*SCALE,   0.0*SCALE,   PI]],
  #  x, y, th - Goalkick-Attack Formation
  [[-3.8*SCALE,   0.0*SCALE, 0],
   [-2.5*SCALE,    0.45*SCALE, 0],
   [-2.5*SCALE,   -0.45*SCALE, 0],
   [-1.5*SCALE,     0.8*SCALE, 0],
   [-1.5*SCALE,    -0.8*SCALE, 0]],
  #  x, y, th - Goalkick-Defense Formation
  [[-3.8*SCALE,   0.0*SCALE, PI / 2],
   [-0.5*SCALE,   0.8*SCALE, 0],
   [-0.5*SCALE,  -0.8*SCALE, 0],
   [0.5*SCALE,    0.45*SCALE, 0],
   [0.5*SCALE,   -0.45*SCALE, 0]],
  #  x, y, th - Corner AD - Attack-Attack Formation
  [[-3.8*SCALE,   0.0*SCALE, PI / 2],
   [2.25*SCALE, -1.0*SCALE, PI / 2],
   [3.25*SCALE, -1.0*SCALE, PI / 2],
   [2.25*SCALE,  0.0*SCALE,      0],
   [2.75*SCALE, -2.0*SCALE, PI / 2]],
  #  x, y, th - Corner AD - Attack-Defense Formation
  [[-3.8*SCALE,   0.0*SCALE, PI / 2],
   [-3.25*SCALE,  0.5*SCALE, PI / 2],
   [-3.25*SCALE, -0.5*SCALE, PI / 2],
   [-2.25*SCALE,  0.5*SCALE, PI / 2],
   [-2.25*SCALE, -0.5*SCALE, PI / 2]],
  #  x, y, th - Corner AD - Defense-Attack Formation
  [[-3.8*SCALE,   0.0*SCALE, PI / 2],
   [-2.25*SCALE,  1.0*SCALE, 3*PI / 2],
   [-3.25*SCALE,  1.0*SCALE, 3*PI / 2],
   [-3.25*SCALE,  0.0*SCALE,        0],
   [-2.75*SCALE,  2.0*SCALE, 3*PI / 2]],
  #  x, y, th - Corner AD - Defense-Defense Formation
  [[-3.8*SCALE,   0.0*SCALE, PI / 2],
   [-1.5*SCALE,   0.45*SCALE, 0],
   [-1.5*SCALE,  -0.45*SCALE, 0],
   [-0.5*SCALE,   0.8*SCALE, 0],
   [-0.5*SCALE,  -0.8*SCALE, 0]],
  #  x, y, th - Corner BC - Attack-Attack Formation
  [[-3.8*SCALE,   0.0*SCALE, PI / 2],
   [3.25*SCALE,  1.0*SCALE, 3*PI / 2],
   [2.25*SCALE,  1.0*SCALE, 3*PI / 2],
   [2.25*SCALE,  0.0*SCALE,        0],
   [2.75*SCALE,  2.0*SCALE, 3*PI / 2]],
  #  x, y, th - Corner BC - Attack-Defense Formation
  [[-3.8*SCALE,   0.0*SCALE, PI / 2],
   [-3.25*SCALE,  0.5*SCALE, 3*PI / 2],
   [-3.25*SCALE, -0.5*SCALE, 3*PI / 2],
   [-2.25*SCALE,  0.5*SCALE, 3*PI / 2],
   [-2.25*SCALE, -0.5*SCALE, 3*PI / 2]],
  #  x, y, th - Corner BC - Defense-Attack Formation
  [[-3.8*SCALE,   0.0*SCALE, PI / 2],
   [-3.25*SCALE, -1.0*SCALE, PI / 2],
   [-2.25*SCALE, -1.0*SCALE, PI / 2],
   [-3.25*SCALE,  0.0*SCALE, 0],
   [-2.75*SCALE, -2.0*SCALE, PI / 2]],
  #  x, y, th - Corner BC - Defense-Defense Formation
  [[-3.8*SCALE,   0.0*SCALE, PI / 2],
   [-1.5*SCALE,   0.45*SCALE, 0],
   [-1.5*SCALE,  -0.45*SCALE, 0],
   [-0.5*SCALE,   0.8*SCALE, 0],
   [-0.5*SCALE,  -0.8*SCALE, 0]],
  #  x, y, th - Penaltykick - Attack Formation
  [[-3.8*SCALE,   0.0*SCALE, PI / 2],
   [0.5*SCALE,  -0.8*SCALE, 0],
   [1.0*SCALE,  -0.8*SCALE, 0],
   [1.5*SCALE,  -0.8*SCALE, 0],
   [2.0*SCALE,   0.0*SCALE, 0]],
  #  x, y, th - Penaltykick - Defense Formation
  [[-3.8*SCALE,   0.0*SCALE,  PI / 2],
   [-1.5*SCALE,  -0.8*SCALE,  PI / 2],
   [-1.5*SCALE,  -1.05*SCALE, PI / 2],
   [-1.25*SCALE, -0.8*SCALE,  PI / 2],
   [-1.25*SCALE, -1.05*SCALE, PI / 2]],
   #  x, y, th - Kickoff Formation
  [[-3.8*SCALE,   0.0*SCALE, PI / 2],
   [-2.25*SCALE,  1.0*SCALE, 0],
   [-2.25*SCALE, -1.0*SCALE, 0],
   [-0.5*SCALE,  0.0*SCALE,   0],
   [-0.4*SCALE,   1.0*SCALE,   0]]
]
FORMATION_DEFAULT = 0
FORMATION_KICKOFF = 1
FORMATION_GOALKICK_A = 2
FORMATION_GOALKICK_D = 3
FORMATION_CAD_AA = 4
FORMATION_CAD_AD = 5
FORMATION_CAD_DA = 6
FORMATION_CAD_DD = 7
FORMATION_CBC_AA = 8
FORMATION_CBC_AD = 9
FORMATION_CBC_DA = 10
FORMATION_CBC_DD = 11
FORMATION_PENALTYKICK_A = 12
FORMATION_PENALTYKICK_D = 13
FORMATION_KICKTEST = 14

ROBOT_FOUL_POSTURE = [
 [-4.05*SCALE, -0.85*SCALE, 0],
 [-4.05*SCALE, -1.15*SCALE, 0],
 [-4.05*SCALE, -1.45*SCALE, 0],
 [-4.05*SCALE, -1.75*SCALE, 0],
 [-4.05*SCALE, -2.05*SCALE, 0],
]
BALL_POSTURE = [
 [0.0*SCALE,  0.0*SCALE],
 [-3.25*SCALE,  0.0*SCALE],
 [-1.5*SCALE,  1.0*SCALE],
 [-1.5*SCALE, -1.0*SCALE],
 [1.5*SCALE,  1.0*SCALE],
 [1.5*SCALE, -1.0*SCALE],
 [-2.75*SCALE,  1.5*SCALE],
 [2.95*SCALE,  0.0*SCALE],
 [-0.5*SCALE + BALL_RADIUS + 0.005, 0.0*SCALE]
]
BALL_DEFAULT = 0
BALL_GOALKICK = 1
BALL_RELOCATION_A = 2
BALL_RELOCATION_B = 3
BALL_RELOCATION_C = 4
BALL_RELOCATION_D = 5
BALL_CORNERKICK = 6
BALL_PENALTYKICK = 7
BALL_KICKTEST = 8

# Server settings
SERVER_IP = '127.0.0.1'
SERVER_PORT = 5003

KEY_LENGTH = 10

# Game settings
WAIT_READY_MS = 30 * 1000  # ms
WAIT_KILL_MS = 30 * 1000  # ms
WAIT_STABLE_MS = 1 * 1000  # ms
WAIT_GOAL_MS = 3 * 1000  # ms
WAIT_VIEW_MS = 1 * 1000  # ms
WAIT_END_MS = 3 * 1000  # ms
DEFAULT_GAME_TIME_MS = 300 * 1000  # ms
PERIOD_MS = 50  # ms
PA_THRESHOLD_A = 2  # penalty area robot limit for attacking team
PA_THRESHOLD_D = 3  # penalty area robot limit for defending team
DEADLOCK_SENTOUT_NUMBER = 2  # number of robots sent out when a deadlock happens
SENTOUT_DURATION_MS = 5 * 1000  # ms
FALL_TIME_MS = 3 * 1000  # ms
DEADLOCK_DURATION_MS = 4 * 1000  # ms
DEADLOCK_THRESHOLD = 0.4  # m/s
CROWDLOCK_DURATION_MS = 7 * 1000 # m/s
CROWDLOCK_THRESHOLD = 3
KICKOFF_TIME_LIMIT_MS = 3 * 1000  # ms
KICKOFF_BORDER = 0.5*SCALE  # m
GOALKICK_TIME_LIMIT_MS = 3 * 1000  # ms
CORNERKICK_TIME_LIMIT_MS = 3 * 1000  # ms
PENALTYKICK_TIME_LIMIT_MS = 3 * 1000  # ms
IOPA_TIME_LIMIT_MS = 1 * 1000  # ms
GK_NIPA_TIME_LIMIT_MS = 1 * 1000  # ms
NUM_COMMENTS = 3
MSG_MAX_SIZE = 90000  # bytes
NONE = 0
GAME_START = 1
SCORE_RED_TEAM = 2
SCORE_BLUE_TEAM = 3
GAME_END = 4
DEADLOCK = 5
GOALKICK = 6
CORNERKICK = 7
PENALTYKICK = 8
HALFTIME = 9
EPISODE_END = 10
CODEWORDS = [0b000000000, 0b000011111, 0b011100011, 0b101101100, 0b110110101]

# Roles
TEAM_RED = 0
TEAM_BLUE = 1
COMMENTATOR = 2
REPORTER = 3
ROLES = [TEAM_RED, TEAM_BLUE, COMMENTATOR, REPORTER]
TEAMS = [TEAM_RED, TEAM_BLUE]

# Sounds
KICK_SOUND = 0
WHISTLE_SOUND = 1
WHISTLE_LONG_SOUND = 2
WHISTLE_2_SOUND = 3
WHISTLE_3_SOUND = 4
GOAL_SOUND = 5

# Replay
REPLAY_THRESHOLD = 3 * 1000 + WAIT_GOAL_MS #ms 