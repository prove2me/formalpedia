-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedCusp_pullback_of_bound
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalClearedCusp_pullback_of_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:12:26.706218+00:00
-- url     : https://prove2.me/theorems/a7c84b33-afcc-4128-9f9b-0e0f468bac4b
-- title:
--   Tanner Lifted Product: lps Original Cleared Cusp pullback of bound
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Cleared Cusp pullback of bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L120-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L120-L138

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalClearedCusp_pullback_of_bound
    (M : ℕ) (hM : 0 < M) (B : ℕ)
    (P : Polynomial (Polynomial ℂ))
    (hB : lpsOriginalClearingBound M P ≤ B) (τ : ℍ) :
    lpsOriginalClearedCusp M B P (Function.Periodic.qParam 1 (τ : ℂ)) =
      (Function.Periodic.qParam 1 (τ : ℂ)) ^ B *
        P.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ))
          (lpsOriginalJDilated M hM τ) := by sorry
