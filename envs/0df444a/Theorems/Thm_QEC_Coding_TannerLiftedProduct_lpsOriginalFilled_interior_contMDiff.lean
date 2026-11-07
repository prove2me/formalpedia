-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_interior_contMDiff
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilled_interior_contMDiff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:01:07.012757+00:00
-- url     : https://prove2.me/theorems/ff20f66a-1624-44fd-891a-8ba01a83c175
-- title:
--   Tanner Lifted Product: lps Original Filled interior cont MDiff
-- statement:
--   The actual original interior inclusion remains complex analytic in the preserved lifted charts.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledAnalytic.lean#L144-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledAnalytic.lean#L144-L161

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilled_interior_contMDiff (N : ℕ) [NeZero N] (hN : 4∣N) :
    letI := lpsOriginalFilledTopology N
    letI := lpsGamma0QuotientChartedSpace N hN
    letI := lpsOriginalFilledChartedSpace N hN
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (Sum.inl : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ → LPSOriginalFilledCurve N) := by sorry
