-- Prove2me | Theorems.Thm_P2M_Csg_rpsCSG_reachBounded_initial_succ__f2e1863eab60
-- name    : P2M_Csg_rpsCSG_reachBounded_initial_succ__f2e1863eab60
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:46:50.937126+00:00
-- url     : https://prove2.me/theorems/c9ab3e7c-a444-4dbe-aa09-cae9bc698f1b
-- title:
--   P2 M Csg rps CSG reach Bounded initial succ  f2e1863eab60: P2 M Csg rps CSG reach Bounded initial succ  f2e1863eab60
-- statement:
--   **The payoff.** The recursion reduces to a single term: `x_{k+1} = (1 + d_k) / 3`, matching the
--       hand-derivation worked out before any of this was written.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L301-L305
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L301-L305

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
set_option autoImplicit true
open Csg

theorem P2M_Csg_rpsCSG_reachBounded_initial_succ__f2e1863eab60 (k : ℕ) :
    rpsCSG.reachBounded rpsGoalWin2 (k + 1) .initial =
      (1 + rpsCSG.reachBounded rpsGoalWin2 k .draw) / 3 := by sorry

alias «Csg».«rpsCSG_reachBounded_initial_succ'» := P2M_Csg_rpsCSG_reachBounded_initial_succ__f2e1863eab60
