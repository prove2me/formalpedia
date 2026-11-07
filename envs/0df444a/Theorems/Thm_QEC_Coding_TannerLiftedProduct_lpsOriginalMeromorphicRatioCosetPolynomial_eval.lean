-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicRatioCosetPolynomial_eval
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicRatioCosetPolynomial_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:36:36.109891+00:00
-- url     : https://prove2.me/theorems/0ed4fd4d-4993-4c66-8c07-9bed0bf38a16
-- title:
--   Tanner Lifted Product: lps Original Meromorphic Ratio Coset Polynomial eval
-- statement:
--   The actual coset product evaluates to the genuine modular-form norm.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicDegreeBound.lean#L63-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicDegreeBound.lean#L63-L72

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicRatioCosetPolynomial_eval
    (N : ℕ) [NeZero N] (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k)
    (τ : ℍ) (c : ℂ) :
    (lpsOriginalMeromorphicRatioCosetPolynomial N k A B τ).eval c =
      lpsOriginalMeromorphicRatioNorm N k A B c τ := by sorry
