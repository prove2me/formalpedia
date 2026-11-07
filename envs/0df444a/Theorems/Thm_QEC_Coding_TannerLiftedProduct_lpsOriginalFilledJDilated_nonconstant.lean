-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJDilated_nonconstant
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJDilated_nonconstant
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T23:28:21.36896+00:00
-- url     : https://prove2.me/theorems/62a3b4d8-b8ec-46a7-969f-f96c77fab46f
-- title:
--   Tanner Lifted Product: lps Original Filled JDilated nonconstant
-- statement:
--   Nonconstancy of the same filled original meromorphic j(Ntau) follows by its actual orbit projection; used by the root fixture and original function-field successor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L290-L293
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L290-L293

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJDilated_nonconstant (N : ℕ) (hN : 0<N) :
    ¬∃ c : ℂ, ∀ x : LPSOriginalFilledCurve N, lpsOriginalFilledJDilated N hN x=c := by sorry
