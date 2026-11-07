-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilated_holomorphic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJDilated_holomorphic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:06:56.129689+00:00
-- url     : https://prove2.me/theorems/fb2e48c4-6798-4903-a0d6-b402c6852a18
-- title:
--   Tanner Lifted Product: lps Original JDilated holomorphic
-- statement:
--   The actual positive-determinant dilation and genuine holomorphic j prove j(Ntau) holomorphic on the upper half plane; used by interior chart analyticity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L62-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L62-L66

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJDilated_holomorphic (N : ℕ) (hN : 0<N) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (lpsOriginalJDilated N hN) := by sorry
