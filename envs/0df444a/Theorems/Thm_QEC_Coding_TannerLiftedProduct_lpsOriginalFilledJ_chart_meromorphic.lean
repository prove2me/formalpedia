-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJ_chart_meromorphic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJ_chart_meromorphic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:18:10.666003+00:00
-- url     : https://prove2.me/theorems/1d3f1991-200a-48c9-8f98-84d056c74429
-- title:
--   Tanner Lifted Product: lps Original Filled J chart meromorphic
-- statement:
--   Meromorphy at every target point of every actual preferred chart of the same original filled curve; immediate input to its original meromorphic function field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularFunction.lean#L361-L377
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularFunction.lean#L361-L377

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Analysis.Meromorphic.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJ_chart_meromorphic (N : ℕ) [NeZero N] (hN : 4∣N)
    (x : LPSOriginalFilledCurve N) (z : ℂ)
    (hz : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      z∈(chartAt ℂ x).target) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    MeromorphicAt (fun w : ℂ => lpsOriginalFilledJ N ((chartAt ℂ x).symm w)) z := by sorry
