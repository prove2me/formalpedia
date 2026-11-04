-- Prove2me | Theorems.Thm_ThreeSum_WeightedFrozenQueryCost_polynomial_product_counts
-- name    : ThreeSum.WeightedFrozenQueryCost.polynomial_product_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:13:20.129755+00:00
-- url     : https://prove2.me/theorems/a2c2eb60-21d3-46ba-94a3-4e1dd5a9c4e7
-- title:
--   Weighted Frozen Query Cost: polynomial product counts
-- statement:
--   The Weighted Frozen Query Cost construction uses the polynomial product counts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenQueryCost.lean#L131-L142
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenQueryCost.lean#L131-L142

import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Definitions.Def_Submission_Weighted_FrozenQueryCost
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedFrozenQueryCost
open Finset WeightedCache WeightedEnumeration

theorem ThreeSum.WeightedFrozenQueryCost.polynomial_product_counts {N : ℕ} (Q : Word N) (z : ℝ) :
    (∏ i : Fin N, (if Q i=0 then 1 else if Q i=1 then 1+z^512 else 1+z^513+z^1025)) =
      (1+z^512)^TernaryJointType.digitCount Q 1 *
        (1+z^513+z^1025)^TernaryJointType.digitCount Q 2 := by sorry
