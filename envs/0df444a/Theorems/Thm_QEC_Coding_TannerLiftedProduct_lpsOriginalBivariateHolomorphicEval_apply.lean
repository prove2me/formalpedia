-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalBivariateHolomorphicEval_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalBivariateHolomorphicEval_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:15:53.365245+00:00
-- url     : https://prove2.me/theorems/1fd0b88f-512d-4081-a1c7-1b232610d39f
-- title:
--   Tanner Lifted Product: lps Original Bivariate Holomorphic Eval apply
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Bivariate Holomorphic Eval apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L169-L188
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L169-L188

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalBivariateHolomorphicEval_apply
    (M : ℕ) (hM : 0 < M) (P : Polynomial (Polynomial ℂ)) (τ : ℍ) :
    (lpsOriginalBivariateHolomorphicEval M hM P).val τ =
      P.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ))
        (lpsOriginalJDilated M hM τ) := by sorry
