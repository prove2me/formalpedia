-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_projection_contMDiff
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilled_projection_contMDiff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:59:41.626843+00:00
-- url     : https://prove2.me/theorems/518bff98-6587-4b12-95a7-f70037cbb155
-- title:
--   Tanner Lifted Product: lps Original Filled projection cont MDiff
-- statement:
--   The original upper-half-plane orbit projection into the same filled curve is complex analytic.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledAnalytic.lean#L164-L173
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledAnalytic.lean#L164-L173

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilled_projection_contMDiff (N : ℕ) [NeZero N] (hN : 4∣N) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun τ : ℍ => (Sum.inl (Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) τ) : LPSOriginalFilledCurve N)) := by sorry
