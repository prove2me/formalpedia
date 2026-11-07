-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJDilated_chart_meromorphic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJDilated_chart_meromorphic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:19:31.452801+00:00
-- url     : https://prove2.me/theorems/038f0603-f66d-4c7f-8165-e4b7524f0e1b
-- title:
--   Tanner Lifted Product: lps Original Filled JDilated chart meromorphic
-- statement:
--   Meromorphy at every target point of every actual preferred chart of the same original filled curve, including its cusps; used by the root fixture and forthcoming original j/jN function-field construction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L395-L411
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDilatedModularFunction.lean#L395-L411

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJDilated_chart_meromorphic (N : ℕ) [NeZero N] (hpos : 0<N) (hN : 4∣N)
    (x : LPSOriginalFilledCurve N) (z : ℂ)
    (hz : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      z∈(chartAt ℂ x).target) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    MeromorphicAt (fun w : ℂ => lpsOriginalFilledJDilated N hpos ((chartAt ℂ x).symm w)) z := by sorry
