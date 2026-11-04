-- Prove2me | Theorems.Thm_ThreeSum_WeightedFrozenQueryCost_digitCost_eq
-- name    : ThreeSum.WeightedFrozenQueryCost.digitCost_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:13:11.726378+00:00
-- url     : https://prove2.me/theorems/58762fc3-74db-4db4-8424-135a8a441379
-- title:
--   Weighted Frozen Query Cost: digit Cost eq
-- statement:
--   The Weighted Frozen Query Cost construction uses the digit Cost eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenQueryCost.lean#L26-L27
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenQueryCost.lean#L26-L27

import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Definitions.Def_Submission_Weighted_FrozenQueryCost
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_digitCost_eq

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedFrozenQueryCost
open Finset WeightedCache WeightedEnumeration

theorem ThreeSum.WeightedFrozenQueryCost.digitCost_eq (d : Fin 3) : digitCost d.val = c d := by sorry
