-- Prove2me | Theorems.Thm_ThreeSum_WeightedFrozenQueryCost_cost_update_drop
-- name    : ThreeSum.WeightedFrozenQueryCost.cost_update_drop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:13:19.807141+00:00
-- url     : https://prove2.me/theorems/4b2adf04-c3a2-4c5e-b020-7d3af7a91b6f
-- title:
--   Weighted Frozen Query Cost: cost update drop
-- statement:
--   The Weighted Frozen Query Cost construction uses the cost update drop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenQueryCost.lean#L52-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenQueryCost.lean#L52-L56

import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Definitions.Def_Submission_Weighted_FrozenQueryCost
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedFrozenQueryCost
open Finset WeightedCache WeightedEnumeration

theorem ThreeSum.WeightedFrozenQueryCost.cost_update_drop {N : ℕ} (R : Word N) (i : Fin N) (d : Fin 3)
    (hd : d≤R i) :
    cacheCost (Function.update R i d)=cacheCost R-(digitCost (R i).val-digitCost d.val) := by sorry
