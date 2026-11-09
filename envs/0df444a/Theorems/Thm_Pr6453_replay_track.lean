-- Prove2me | Theorems.Thm_Pr6453_replay_track
-- name    : Pr6453.replay_track
-- status  : Proved
-- author  : @gustasmickus
-- created : 2026-11-08T22:05:45.775745+00:00
-- url     : https://prove2.me/theorems/cad58ac3-a5bf-47f3-9824-ec01223a73d0
-- title:
--   PR #6453: each column's frame is what its own track computes
-- statement:
--   Each column's final frame is exactly what that column's own track computes. A frame is written only by the events naming a column — move, initialisation, clear — and each acts on its own column alone, so the frame chart factored into 1095 independent one-dimensional tracks agrees, column by column, with the full replay. This is the structural form of the per-stage statement and reduces the legality question for a 17 926-event word to 1095 short one-dimensional checks.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4: the guarded replay of research/p104-clean-piggyback/construct.py.

import Definitions.Def_Pr6453_Locality
import Definitions.Def_Pr6453_Track

set_option autoImplicit false

namespace Pr6453

theorem replay_track {n : ℕ} (p : List (Event n)) (fr : Fin n → Option ℕ) (c : Fin n)
    (g : Fin n → Option ℕ) (h : replayF? p fr = some g) :
    trackRun c p (fr c) = some (g c) := by
  sorry

end Pr6453
