-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledChartMeromorphic_finite_nonanalytic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledChartMeromorphic_finite_nonanalytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:29:37.957058+00:00
-- url     : https://prove2.me/theorems/16630a0d-1325-4496-a513-dea6054ec41b
-- title:
--   Tanner Lifted Product: lps Original Filled Chart Meromorphic finite nonanalytic
-- statement:
--   Compactness makes the actual nonanalytic set of any meromorphic function finite.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicPoleClearing.lean#L54-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicPoleClearing.lean#L54-L75

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicRestriction
import Mathlib.Analysis.Analytic.Polynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledChartMeromorphic_finite_nonanalytic
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    {x : LPSOriginalFilledCurve N |
      ¬ ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x}.Finite := by sorry
