-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphic_clear_by_analytic_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphic_clear_by_analytic_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:30:47.677165+00:00
-- url     : https://prove2.me/theorems/74b3d9f0-8903-4e24-b8fc-0f4e1e75a1ac
-- title:
--   Tanner Lifted Product: lps Original Meromorphic clear by analytic zero
-- statement:
--   A genuine analytic zero clears a local meromorphic pole after a sufficiently large power.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicPoleClearing.lean#L80-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicPoleClearing.lean#L80-L96

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicRestriction
import Mathlib.Analysis.Analytic.Polynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphic_clear_by_analytic_zero
    (f g : ℂ → ℂ) (x : ℂ) (hf : MeromorphicAt f x) (hg : AnalyticAt ℂ g x) :
    ∃ n : ℕ, AnalyticAt ℂ (fun z => (g z-g x)^n * f z) x := by sorry
