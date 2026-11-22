-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_hypercube_card_mul_inv_two_pow_succ_lt_one
-- name    : PebblingLean.Hypercube.hypercube_card_mul_inv_two_pow_succ_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:51:13.760153+00:00
-- url     : https://prove2.me/theorems/85c0f412-679e-4c97-9616-681f389537b7
-- title:
--   Hypercube: hypercube card mul inv two pow succ lt one
-- statement:
--   The Hypercube construction uses the hypercube card mul inv two pow succ lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1820-L1826
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1820-L1826

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
open FiniteProbability

theorem PebblingLean.Hypercube.hypercube_card_mul_inv_two_pow_succ_lt_one (n : ℕ) :
    (Fintype.card (HypercubeVertex n) : ℚ) *
        ((1 : ℚ) / (2 ^ (n + 1) : ℚ)) < 1 := by sorry
