-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegralFixInfinity_translation
-- name    : QEC.Coding.TannerLiftedProduct.lpsIntegralFixInfinity_translation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:21:43.293192+00:00
-- url     : https://prove2.me/theorems/52155381-0a06-4ba4-819d-05bce49bd657
-- title:
--   Tanner Lifted Product: lps Integral Fix Infinity translation
-- statement:
--   An actual integral determinant-one matrix fixing infinity is a signed translation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspWidths.lean#L97-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspWidths.lean#L97-L122

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.NumberTheory.ModularForms.Cusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspWidths
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsIntegralFixInfinity_translation (g : GL (Fin 2) ℝ)
    (hg : g ∈ (Matrix.SpecialLinearGroup.mapGL (n:=Fin 2) (R:=ℤ) ℝ).range)
    (hc : g 1 0=0) :
    ∃ x : ℝ, g=Matrix.GeneralLinearGroup.upperRightHom x ∨
      g= -Matrix.GeneralLinearGroup.upperRightHom x := by sorry
