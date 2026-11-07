-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJDilated_projection
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJDilated_projection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:16:38.929193+00:00
-- url     : https://prove2.me/theorems/3cdc2ac4-6020-4188-b87b-b643623b45c0
-- title:
--   Tanner Lifted Product: lps Original Filled JDilated projection
-- statement:
--   The same genuine upper-half-plane j(Ntau) is recovered by the original filled projection; used by interior chart analyticity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L286-L287
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L286-L287

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJDilated_projection (N : ℕ) (hN : 0<N) (τ : ℍ) :
    lpsOriginalFilledJDilated N hN (Sum.inl ⟦τ⟧)=lpsOriginalJDilated N hN τ := by sorry
