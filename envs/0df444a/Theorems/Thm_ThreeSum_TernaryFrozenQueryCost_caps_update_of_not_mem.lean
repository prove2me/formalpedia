-- Prove2me | Theorems.Thm_ThreeSum_TernaryFrozenQueryCost_caps_update_of_not_mem
-- name    : ThreeSum.TernaryFrozenQueryCost.caps_update_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:10:57.584736+00:00
-- url     : https://prove2.me/theorems/56e1d7ab-7d94-4026-a8d6-deb6d32f5990
-- title:
--   Ternary Frozen Query Cost: caps update of not mem
-- statement:
--   The Ternary Frozen Query Cost construction uses the caps update of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryCost.lean#L38-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryCost.lean#L38-L45

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryFrozenQueryCost
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryFrozenQueryCost.caps_update_of_not_mem {N : ℕ} (coords : List (Fin N)) (R : TritWord N)
    (i : Fin N) (d : Fin 3) (hi : i∉coords) :
    caps coords (Function.update R i d)=caps coords R := by sorry
