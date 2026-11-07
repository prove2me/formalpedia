-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNInFractionField_integralQ
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJNInFractionField_integralQ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:57:47.811526+00:00
-- url     : https://prove2.me/theorems/f38a80ac-552e-433f-bf1d-7eece06ba258
-- title:
--   Tanner Lifted Product: lps Original JNIn Fraction Field integral Q
-- statement:
--   Integrality of SAME original jN over the true embedded rational function field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalFunctionField.lean#L153-L158
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalFunctionField.lean#L153-L158

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJNInFractionField_integralQ (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    IsIntegral (FractionRing (Polynomial ℚ)) (lpsOriginalJNInFractionField N hN) := by sorry
