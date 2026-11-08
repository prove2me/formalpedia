-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldLocalOrder_clear_power
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFieldLocalOrder_clear_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:07:18.497201+00:00
-- url     : https://prove2.me/theorems/14de1a25-394c-49b7-9b8a-d2a85717596c
-- title:
--   Tanner Lifted Product: lps Original Field Local Order clear power
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Field Local Order clear power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFiniteInteriorFibres.lean#L64-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFiniteInteriorFibres.lean#L64-L87

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFieldIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFiniteInteriorFibres
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteInteriorDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteInteriorDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteInteriorDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteInteriorDictionary004
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFieldLocalOrder_clear_power (x : LPSOriginalFilledCurve N) (a f : K)
    (ha : 0 < lpsOriginalFieldLocalOrder N hN hpos x a) (hane : a ≠ 0) :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m →
      0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (a^m*f) := by sorry
