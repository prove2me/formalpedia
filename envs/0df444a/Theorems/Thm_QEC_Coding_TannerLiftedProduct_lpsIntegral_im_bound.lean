-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegral_im_bound
-- name    : QEC.Coding.TannerLiftedProduct.lpsIntegral_im_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:37:50.327783+00:00
-- url     : https://prove2.me/theorems/38cfa2e0-c99a-4e58-972d-e0d59938a0ea
-- title:
--   Tanner Lifted Product: lps Integral im bound
-- statement:
--   Every actual integral matrix bounds transformed height by max(y,1/y).
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactCore.lean#L101-L130
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactCore.lean#L101-L130

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsIntegral_im_bound (g : GL (Fin 2) ℝ)
    (hg : g∈(Matrix.SpecialLinearGroup.mapGL (n:=Fin 2) (R:=ℤ) ℝ).range) (τ : ℍ) :
    (g • τ).im≤ max τ.im (1/τ.im) := by sorry
