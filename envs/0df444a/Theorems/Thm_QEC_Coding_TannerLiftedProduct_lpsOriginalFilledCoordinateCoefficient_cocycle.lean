-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCoordinateCoefficient_cocycle
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCoordinateCoefficient_cocycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:47:49.236201+00:00
-- url     : https://prove2.me/theorems/eccaf439-35e4-4e7b-8ff6-bc9113488bb0
-- title:
--   Tanner Lifted Product: lps Original Filled Coordinate Coefficient cocycle
-- statement:
--   All four actual preferred-chart transitions satisfy the derivative-weighted cocycle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialGluing.lean#L198-L220
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalDifferentialGluing.lean#L198-L220

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialGluing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCoordinateCoefficient_cocycle (N : ℕ) [NeZero N]
    (hN : 4∣N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (x y : LPSOriginalFilledCurve N) (z : ℂ)
    (hz : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      z∈((chartAt ℂ x).symm.trans (chartAt ℂ y)).source) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    let e := (chartAt ℂ x).symm.trans (chartAt ℂ y)
    lpsOriginalFilledCoordinateCoefficient N f y (e z) * deriv e z =
      lpsOriginalFilledCoordinateCoefficient N f x z := by sorry
