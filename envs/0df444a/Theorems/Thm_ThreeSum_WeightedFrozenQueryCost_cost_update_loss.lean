-- Prove2me | Theorems.Thm_ThreeSum_WeightedFrozenQueryCost_cost_update_loss
-- name    : ThreeSum.WeightedFrozenQueryCost.cost_update_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:13:31.592143+00:00
-- url     : https://prove2.me/theorems/9f989064-fd32-495e-9c4d-83b6d7a64a56
-- title:
--   Weighted Frozen Query Cost: cost update loss
-- statement:
--   The Weighted Frozen Query Cost construction uses the cost update loss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenQueryCost.lean#L29-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenQueryCost.lean#L29-L50

import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Definitions.Def_Submission_Weighted_FrozenQueryCost
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedFrozenQueryCost
open Finset WeightedCache WeightedEnumeration

theorem ThreeSum.WeightedFrozenQueryCost.cost_update_loss {N : ℕ} (R : Word N) (i : Fin N) (d : Fin 3)
    (hd : d ≤ R i) :
    cacheCost (Function.update R i d) + (digitCost (R i).val - digitCost d.val) =
      cacheCost R := by sorry
