-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalField_polynomial_clear_away
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalField_polynomial_clear_away
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:14:00.348654+00:00
-- url     : https://prove2.me/theorems/1c91735a-9787-42a2-b6e5-3d33950380cb
-- title:
--   Tanner Lifted Product: lps Original Field polynomial clear away
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Field polynomial clear away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPoleClearingAway.lean#L33-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPoleClearingAway.lean#L33-L86

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFiniteInteriorFibres
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPoleClearingAway
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular BigOperators
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalPoleAwayDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalPoleAwayDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalPoleAwayDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalPoleAwayDictionary004
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalField_polynomial_clear_away (f : K) (α : ℂ)
    (hα : ∀ x : Q, lpsOriginalFilledJ N (Sum.inl x) = α →
      0 ≤ lpsOriginalFieldLocalOrder N hN hpos (Sum.inl x) f) :
    ∃ H : P, H.eval α ≠ 0 ∧ IsIntegral P (algebraMap P K H*f) := by sorry
