-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQParam_smul_analytic
-- name    : QEC.Coding.TannerLiftedProduct.lpsQParam_smul_analytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:42:55.477221+00:00
-- url     : https://prove2.me/theorems/c096ad90-746a-4af5-b578-b72ed88b075d
-- title:
--   Tanner Lifted Product: lps QParam smul analytic
-- statement:
--   The genuine q exponential composed with a positive-determinant Mobius action is complex analytic.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspAnalytic.lean#L19-L26
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspAnalytic.lean#L19-L26

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferentialCharts
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspAnalytic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsQParam_smul_analytic (h : ℝ) (g : GL (Fin 2) ℝ)
    (hg : 0<g.val.det) (τ : ℍ) :
    AnalyticAt ℂ (fun z : ℂ => Function.Periodic.qParam h ((g • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) τ := by sorry
