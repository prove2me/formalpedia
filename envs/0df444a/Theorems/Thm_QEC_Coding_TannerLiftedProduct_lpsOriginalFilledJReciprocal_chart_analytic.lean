-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJReciprocal_chart_analytic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJReciprocal_chart_analytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:00:27.705703+00:00
-- url     : https://prove2.me/theorems/4dd096b6-ed22-45f0-80db-beb1a7a0e29c
-- title:
--   Tanner Lifted Product: lps Original Filled JReciprocal chart analytic
-- statement:
--   Reciprocal analyticity at every target point of every actual preferred chart.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJNormalization.lean#L159-L176
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJNormalization.lean#L159-L176

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJReciprocal_chart_analytic (N : ℕ) [NeZero N] (hN : 4∣N)
    (a : ℂ) (ho : ∀ τ : ℍ, lpsOriginalJInvariant τ≠a)
    (x : LPSOriginalFilledCurve N) (z : ℂ)
    (hz : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      z∈(chartAt ℂ x).target) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    AnalyticAt ℂ (fun w : ℂ => lpsOriginalFilledJReciprocal N a ((chartAt ℂ x).symm w)) z := by sorry
