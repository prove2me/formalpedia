-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJReciprocal_cusp_analytic_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJReciprocal_cusp_analytic_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:01:07.56446+00:00
-- url     : https://prove2.me/theorems/03b3503b-5462-4c7b-b4fc-b841f9c12c50
-- title:
--   Tanner Lifted Product: lps Original Filled JReciprocal cusp analytic zero
-- statement:
--   Ordinary-neighborhood analyticity at the true cusp zero, including its actual zero value.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJNormalization.lean#L81-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJNormalization.lean#L81-L112

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJReciprocal_cusp_analytic_zero (N : ℕ) [NeZero N] (a : ℂ)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    AnalyticAt ℂ (fun q : ℂ => lpsOriginalFilledJReciprocal N a
      ((lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).symm q)) 0 := by sorry
