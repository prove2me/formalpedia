-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilated_qParam_pullback
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJDilated_qParam_pullback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:04:58.595402+00:00
-- url     : https://prove2.me/theorems/d6eecd10-d490-4203-92eb-0369dbf0a142
-- title:
--   Tanner Lifted Product: lps Original JDilated q Param pullback
-- statement:
--   True nome dilation gives q^N*j(Ntau)=K(q^N); used by its actual limit and the root fixture.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L84-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L84-L88

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJDilated_qParam_pullback (N : ℕ) (hN : 0<N) (τ : ℍ) :
    Function.Periodic.qParam 1 (τ:ℂ)^N*lpsOriginalJDilated N hN τ=
      lpsOriginalJQCoefficient (Function.Periodic.qParam 1 (τ:ℂ)^N) := by sorry
