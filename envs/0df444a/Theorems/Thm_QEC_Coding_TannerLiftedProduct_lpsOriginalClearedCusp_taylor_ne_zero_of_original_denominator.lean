-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedCusp_taylor_ne_zero_of_original_denominator
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalClearedCusp_taylor_ne_zero_of_original_denominator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:18:54.610585+00:00
-- url     : https://prove2.me/theorems/903512e6-edb7-4df0-83e2-1dc4ae2e7c2b
-- title:
--   Tanner Lifted Product: lps Original Cleared Cusp taylor ne zero of original denominator
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Cleared Cusp taylor ne zero of original denominator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L191-L206
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L191-L206

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalClearedCusp_taylor_ne_zero_of_original_denominator
    (M : ℕ) (hM : 0 < M) (B : ℕ) (P : Polynomial (Polynomial ℂ))
    (hB : lpsOriginalClearingBound M P ≤ B)
    (hP : lpsOriginalBivariateHolomorphicEval M hM P ≠ 0) :
    lpsOriginalTaylorSeries (lpsOriginalClearedCusp M B P) ≠ 0 := by sorry
