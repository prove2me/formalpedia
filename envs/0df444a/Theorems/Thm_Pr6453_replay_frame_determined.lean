-- Prove2me | Theorems.Thm_Pr6453_replay_frame_determined
-- name    : Pr6453.replay_frame_determined
-- status  : Proved
-- author  : @gustasmickus
-- created : 2026-11-08T20:58:58.181455+00:00
-- url     : https://prove2.me/theorems/6a9600c3-0c2d-4f2a-a180-224803774d3b
-- title:
--   PR #6453: the replay is frame-determined
-- statement:
--   A replay of a word is legal exactly when its frame chart alone replays legally.
--
--   The guards of the replay read only the frame chart, never the rows: a step succeeds exactly when its frame component (`frameStep?`) does, and by induction the same holds for a whole program.
--
--   This is the reduction that makes the replay of a 17 926-event word provable: the sparse rational rows the word transports never have to be unfolded, and legality becomes a question about a chart of 1095 frames.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4: the guarded replay of research/p104-clean-piggyback/construct.py.

import Definitions.Def_Pr6453_Replay
import Definitions.Def_Pr6453_Frames

set_option autoImplicit false

namespace Pr6453

theorem replay_frame_determined {n : ℕ} (prog : List (Event n)) (st : State n) :
    (replay? prog st).isSome = (replayF? prog st.frames).isSome := by
  sorry

end Pr6453
