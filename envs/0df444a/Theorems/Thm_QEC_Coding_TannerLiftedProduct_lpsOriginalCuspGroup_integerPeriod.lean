-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspGroup_integerPeriod
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspGroup_integerPeriod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:22:02.823607+00:00
-- url     : https://prove2.me/theorems/641ed597-8c65-4ac0-89ed-dfc7c5bc29c9
-- title:
--   Tanner Lifted Product: lps Original Cusp Group integer Period
-- statement:
--   The existing genuine common period is retained, without calling it minimal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspWidths.lean#L71-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspWidths.lean#L71-L73

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.NumberTheory.ModularForms.Cusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspWidths
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspGroup_integerPeriod (N : ℕ) (ρ : SL(2,ℤ)) :
    (N:ℝ) ∈ (lpsOriginalCuspGroup N ρ).strictPeriods := by sorry
