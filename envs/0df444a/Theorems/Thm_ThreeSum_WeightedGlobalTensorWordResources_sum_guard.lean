-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalTensorWordResources_sum_guard
-- name    : ThreeSum.WeightedGlobalTensorWordResources.sum_guard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:42:24.851858+00:00
-- url     : https://prove2.me/theorems/58a9d5b4-ed0a-447e-b165-991b6a5ee55a
-- title:
--   Weighted Global Tensor Word Resources: sum guard
-- statement:
--   The Weighted Global Tensor Word Resources construction uses the sum guard property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryTensorWordResources.lean#L64-L70
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryTensorWordResources.lean#L64-L70

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactoryReady
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_Weighted_Global_TernaryTensorWordResources
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalTensorWordResources
open LightTernaryPairedPolynomial TernaryPairedColumnEnumeration StageBounds

theorem ThreeSum.WeightedGlobalTensorWordResources.sum_guard (K J count V sourceU : ℕ) :
    (count : ℤ)*((J+2)^width K : ℕ)*(polynomial K).bound V≤(word K J count V sourceU : ℤ) := by sorry
