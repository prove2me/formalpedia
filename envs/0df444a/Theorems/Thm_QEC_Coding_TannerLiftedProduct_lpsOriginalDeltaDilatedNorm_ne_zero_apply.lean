-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDeltaDilatedNorm_ne_zero_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaDilatedNorm_ne_zero_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:01:25.165901+00:00
-- url     : https://prove2.me/theorems/e2681d55-39a1-4a8c-924d-5a9bc65972c6
-- title:
--   Tanner Lifted Product: lps Original Delta Dilated Norm ne zero apply
-- statement:
--   The genuine original dilated-Delta finite-coset norm is nowhere zero at every actual upper-half-plane point.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJNormalization.lean#L237-L255
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJNormalization.lean#L237-L255

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaDilatedNorm_ne_zero_apply (N : ℕ) [NeZero N] (hN : 0<N)
    (τ : ℍ) : lpsOriginalDeltaDilatedNorm N hN τ≠0 := by sorry
