-- Prove2me | Theorems.Thm_ThreeSum_TernaryFrozenQueryCost_rank_update_loss
-- name    : ThreeSum.TernaryFrozenQueryCost.rank_update_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:11:01.987105+00:00
-- url     : https://prove2.me/theorems/7976454c-4426-41b9-a473-df2a206612b9
-- title:
--   Ternary Frozen Query Cost: rank update loss
-- statement:
--   The Ternary Frozen Query Cost construction uses the rank update loss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryCost.lean#L24-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryCost.lean#L24-L36

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryFrozenQueryCost
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryFrozenQueryCost.rank_update_loss {N : ℕ} (R : TritWord N) (i : Fin N) (d : Fin 3)
    (hd : d≤R i) : rank (Function.update R i d)+((R i).val-d.val)=rank R := by sorry
