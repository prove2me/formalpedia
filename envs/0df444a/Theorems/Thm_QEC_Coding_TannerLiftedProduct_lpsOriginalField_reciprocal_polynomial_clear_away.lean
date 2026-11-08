-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalField_reciprocal_polynomial_clear_away
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalField_reciprocal_polynomial_clear_away
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:06:02.199693+00:00
-- url     : https://prove2.me/theorems/ade7413c-9d4e-4d57-98df-4fdbd0d9faa0
-- title:
--   Tanner Lifted Product: lps Original Field reciprocal polynomial clear away
-- statement:
--   Construct a polynomial nonzero at a chosen fibre value that clears every other actual reciprocal pole.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalInfinityPoleClearingAway.lean#L35-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalInfinityPoleClearingAway.lean#L35-L90

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityFiniteFibres
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityPoleClearingAway
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular BigOperators
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityPoleClearingAwayDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "S" => lpsOriginalInfinityRegularPoints N hpos hN

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalField_reciprocal_polynomial_clear_away (f : K) (α : ℂ)
    (hα : ∀ x : S, lpsOriginalInfinityCoordinate N hpos hN x = α →
      0 ≤ lpsOriginalFieldLocalOrder N hN hpos x.val f) :
    ∃ H : P, H.eval α ≠ 0 ∧
      (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos).IsIntegralElem
        (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos H*f) := by sorry
