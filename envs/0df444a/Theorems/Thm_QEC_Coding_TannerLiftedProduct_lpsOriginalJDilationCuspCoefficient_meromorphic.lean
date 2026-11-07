-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilationCuspCoefficient_meromorphic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJDilationCuspCoefficient_meromorphic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:18:57.379197+00:00
-- url     : https://prove2.me/theorems/6b6dcfda-f788-44a8-9372-50bbff51b7f2
-- title:
--   Tanner Lifted Product: lps Original JDilation Cusp Coefficient meromorphic
-- statement:
--   The genuine translated analytic numerator and denominator give a meromorphic cusp coefficient at zero; used by the true added-cusp germ.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L259-L263
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L259-L263

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJDilationCuspCoefficient_meromorphic (N : ℕ) [NeZero N]
    (hN : 0<N) (ρ : SL(2,ℤ)) :
    MeromorphicAt (lpsOriginalJDilationCuspCoefficient N hN ρ) 0 := by sorry
