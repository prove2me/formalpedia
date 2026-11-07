-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalThetaLevel_filled_isManifold
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalThetaLevel_filled_isManifold
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T23:24:14.217827+00:00
-- url     : https://prove2.me/theorems/58f29eeb-83c3-4644-80ca-3821eeb33ffe
-- title:
--   Tanner Lifted Product: lps Original Theta Level filled is Manifold
-- statement:
--   Every nonzero original theta level has the genuine filled complex analytic structure, without a spectral or arithmetic magnitude assumption.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledAnalytic.lean#L176-L184
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledAnalytic.lean#L176-L184

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCharts
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspAnalytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalThetaLevel_filled_isManifold (q : ℕ) (hq : q≠0) :
    let : NeZero ((4*q)^2) := ⟨by positivity⟩
    letI := lpsOriginalFilledTopology ((4*q)^2)
    letI := lpsOriginalFilledChartedSpace ((4*q)^2)
      (dvd_pow (dvd_mul_right 4 q) (by decide))
    IsManifold 𝓘(ℂ) ω (LPSOriginalFilledCurve ((4*q)^2)) := by sorry
