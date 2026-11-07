-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicRatioCosetPolynomial_degree
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicRatioCosetPolynomial_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:37:00.812987+00:00
-- url     : https://prove2.me/theorems/f83b7205-42c7-4ab5-a056-6105a9b05ab0
-- title:
--   Tanner Lifted Product: lps Original Meromorphic Ratio Coset Polynomial degree
-- statement:
--   The actual polynomial degree is at most the genuine original coset cardinal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicDegreeBound.lean#L75-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicDegreeBound.lean#L75-L91

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicRatioCosetPolynomial_degree
    (N : ℕ) [NeZero N] (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k) (τ : ℍ) :
    (lpsOriginalMeromorphicRatioCosetPolynomial N k A B τ).natDegree ≤
      Nat.card (LPSOriginalMeromorphicCosets N) := by sorry
