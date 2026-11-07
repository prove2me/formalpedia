-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledChartMeromorphic_eventually_analytic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledChartMeromorphic_eventually_analytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:29:47.359202+00:00
-- url     : https://prove2.me/theorems/9c4072c1-bf84-4e91-a1e0-d73877d4b49e
-- title:
--   Tanner Lifted Product: lps Original Filled Chart Meromorphic eventually analytic
-- statement:
--   Actual local meromorphy implies analyticity away from the chart center.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicPoleClearing.lean#L25-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicPoleClearing.lean#L25-L51

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicRestriction
import Mathlib.Analysis.Analytic.Polynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledChartMeromorphic_eventually_analytic
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (x : LPSOriginalFilledCurve N) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    ∀ᶠ y in 𝓝[≠] x, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F y := by sorry
