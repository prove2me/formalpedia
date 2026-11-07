-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJHolomorphicEvalQ_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJHolomorphicEvalQ_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:58:30.898237+00:00
-- url     : https://prove2.me/theorems/2fe512cd-f9bb-4b0b-952f-8c20f6947fb6
-- title:
--   Tanner Lifted Product: lps Original JHolomorphic Eval Q apply
-- statement:
--   Literal pointwise evaluation identity for the genuine rational polynomial map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalFunctionField.lean#L35-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalFunctionField.lean#L35-L38

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJHolomorphicEvalQ_apply (P : Polynomial ℚ) (τ : ℍ) :
    (lpsOriginalJHolomorphicEvalQ P).val τ=P.eval₂ (algebraMap ℚ ℂ) (lpsOriginalJInvariant τ) := by sorry
