-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCoordinateCoefficient_analytic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCoordinateCoefficient_analytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:47:09.531345+00:00
-- url     : https://prove2.me/theorems/7db4f3e2-4983-4b27-a148-427f0e43c639
-- title:
--   Tanner Lifted Product: lps Original Filled Coordinate Coefficient analytic
-- statement:
--   Every actual preferred-chart target has an analytic differential coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialGluing.lean#L22-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialGluing.lean#L22-L42

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialGluing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCoordinateCoefficient_analytic (N : ℕ) [NeZero N]
    (hN : 4∣N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (x : LPSOriginalFilledCurve N) (z : ℂ)
    (hz : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      z∈(chartAt ℂ x).target) :
    AnalyticAt ℂ (lpsOriginalFilledCoordinateCoefficient N f x) z := by sorry
