-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalTensorWordResources_polynomial_bound
-- name    : ThreeSum.WeightedGlobalTensorWordResources.polynomial_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:45:57.942041+00:00
-- url     : https://prove2.me/theorems/22c54785-de7c-4357-9406-695a130e8444
-- title:
--   Weighted Global Tensor Word Resources: polynomial bound
-- statement:
--   The Weighted Global Tensor Word Resources construction uses the polynomial bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryTensorWordResources.lean#L20-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryTensorWordResources.lean#L20-L25

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactoryReady
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_Weighted_Global_TernaryTensorWordResources
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalTensorWordResources
open LightTernaryPairedPolynomial TernaryPairedColumnEnumeration StageBounds

theorem ThreeSum.WeightedGlobalTensorWordResources.polynomial_bound (K V : ℕ) :
    (polynomial K).bound (V : ℤ)≤(polynomialBound K V : ℤ) := by sorry
