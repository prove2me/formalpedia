-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspGroup_width_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspGroup_width_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T22:28:58.597939+00:00
-- url     : https://prove2.me/theorems/14a4a4dc-03ee-49cc-bc43-d472d0bacef7
-- title:
--   Tanner Lifted Product: lps Original Cusp Group width eq
-- statement:
--   Adjoining minus identity does not change the actual minimal cusp width.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspWidths.lean#L90-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspWidths.lean#L90-L94

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.NumberTheory.ModularForms.Cusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspWidths
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspGroup_width_eq (N : ℕ) (ρ : SL(2,ℤ)) :
    (lpsOriginalCuspGroup N ρ).widthInfty =
      (lpsOriginalCuspGroup N ρ).strictWidthInfty := by sorry
