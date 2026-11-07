-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspGroup_width_positive
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspGroup_width_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:21:06.061216+00:00
-- url     : https://prove2.me/theorems/7825e028-9601-46c4-b847-5e4c8dd8d22e
-- title:
--   Tanner Lifted Product: lps Original Cusp Group width positive
-- statement:
--   The true minimal strict width is positive, derived from the genuine nonzero period.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspWidths.lean#L76-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspWidths.lean#L76-L81

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.NumberTheory.ModularForms.Cusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspWidths
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspGroup_width_positive (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    0 < (lpsOriginalCuspGroup N ρ).strictWidthInfty := by sorry
