-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNHolomorphic_integralQ
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJNHolomorphic_integralQ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T01:18:53.340186+00:00
-- url     : https://prove2.me/theorems/81d5009e-ed9b-4a96-a09f-50db1635db36
-- title:
--   Tanner Lifted Product: lps Original JNHolomorphic integral Q
-- statement:
--   Actual original jN integral over the image of Q[j], using the proved original rational monic relation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalFunctionField.lean#L49-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalFunctionField.lean#L49-L73

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJNHolomorphic_integralQ (N : ℕ) [NeZero N] (hN : 0<N) :
    lpsOriginalJHolomorphicEvalQ.IsIntegralElem
      (lpsOriginalJNHolomorphic N hN) := by sorry
