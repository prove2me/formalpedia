-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_pow_two_sub_eq_mul_half_pow
-- name    : PebblingLean.Hypercube.pow_two_sub_eq_mul_half_pow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:51:51.90515+00:00
-- url     : https://prove2.me/theorems/3f641d8b-5cd0-41d9-ad97-47fae60500cf
-- title:
--   Hypercube: pow two sub eq mul half pow
-- statement:
--   The Hypercube construction uses the pow two sub eq mul half pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L271-L276
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L271-L276

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

theorem PebblingLean.Hypercube.pow_two_sub_eq_mul_half_pow {rOut i : ℕ} (hi : i ≤ rOut) :
    (2 ^ (rOut - i) : ℝ) = (2 ^ rOut : ℝ) * ((1 : ℝ) / 2) ^ i := by sorry
