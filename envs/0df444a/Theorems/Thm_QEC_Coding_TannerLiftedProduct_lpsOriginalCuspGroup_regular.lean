-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspGroup_regular
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspGroup_regular
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-06T22:29:01.912506+00:00
-- url     : https://prove2.me/theorems/5e078dc7-529e-4990-8bc0-5ca3de93ca6c
-- title:
--   Tanner Lifted Product: lps Original Cusp Group regular
-- statement:
--   The genuine strict periods and periods agree for the original cusp group.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspWidths.lean#L42-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspWidths.lean#L42-L44

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.NumberTheory.ModularForms.Cusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspWidths
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspGroup_regular (N : ℕ) (ρ : SL(2,ℤ)) :
    (lpsOriginalCuspGroup N ρ).IsRegularAtInfty := by sorry
