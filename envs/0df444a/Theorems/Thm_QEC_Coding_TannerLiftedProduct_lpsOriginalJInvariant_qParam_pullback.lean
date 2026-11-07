-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJInvariant_qParam_pullback
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJInvariant_qParam_pullback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:02:43.647952+00:00
-- url     : https://prove2.me/theorems/26537d55-e29a-4fec-ae21-f178052b4931
-- title:
--   Tanner Lifted Product: lps Original JInvariant q Param pullback
-- statement:
--   Exact q*j pullback on the original upper half plane; used by the limit and actual minimum-width cusp parametrization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularFunction.lean#L89-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularFunction.lean#L89-L109

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Analysis.Meromorphic.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJInvariant_qParam_pullback (τ : ℍ) :
    Function.Periodic.qParam 1 (τ:ℂ)*lpsOriginalJInvariant τ=
      lpsOriginalJQCoefficient (Function.Periodic.qParam 1 (τ:ℂ)) := by sorry
