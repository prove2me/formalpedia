-- Prove2me | Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicJFunctionCoefficient_eval__80431591df58
-- name    : P2M_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicJFunctionCoefficient_eval__80431591df58
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:38:55.170681+00:00
-- url     : https://prove2.me/theorems/b8961074-9a46-41d9-8072-1ba26a034239
-- title:
--   P2 M QEC Coding Tanner Lifted Product lps Original Meromorphic JFunction Coefficient eval  80431591df58: P2 M QEC Coding Tanner Lifted Product lps Original Meromorphic JFunction Coefficient eval  8043
-- statement:
--   Actual function-valued nested evaluation agrees with literal pointwise evaluation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicDegreeBound.lean#L276-L286
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicDegreeBound.lean#L276-L286

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem P2M_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicJFunctionCoefficient_eval__80431591df58
    (Φ : Polynomial (Polynomial ℂ)) (f : ℂ → ℂ) (z : ℂ) :
    (Φ.eval₂ lpsOriginalMeromorphicJFunctionCoefficient f) z =
      Φ.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant (UpperHalfPlane.ofComplex z)))
        (f z) := by sorry

alias «QEC».«Coding».«TannerLiftedProduct».«lpsOriginalMeromorphicJFunctionCoefficient_eval₂» := P2M_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicJFunctionCoefficient_eval__80431591df58
