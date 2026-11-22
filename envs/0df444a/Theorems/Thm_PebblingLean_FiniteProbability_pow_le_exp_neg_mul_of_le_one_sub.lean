-- Prove2me | Theorems.Thm_PebblingLean_FiniteProbability_pow_le_exp_neg_mul_of_le_one_sub
-- name    : PebblingLean.FiniteProbability.pow_le_exp_neg_mul_of_le_one_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:29.888339+00:00
-- url     : https://prove2.me/theorems/576bbccb-184a-45de-8c7b-7124f765825b
-- title:
--   Finite Probability: pow le exp neg mul of le one sub
-- statement:
--   If a nonnegative one-step moment is at most `1-u`, then its `N`-fold
--   product is at most `exp(-N u)`.  This is the product step in the
--   bounded-nonnegative Chernoff argument.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Concentration.lean#L181-L198
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Concentration.lean#L181-L198

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_PebblingLean_FiniteProbability
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_Concentration
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.FiniteProbability
variable {Ω : Type*}

theorem PebblingLean.FiniteProbability.pow_le_exp_neg_mul_of_le_one_sub {a u : ℝ} (N : ℕ)
    (ha_nonneg : 0 ≤ a) (ha_le : a ≤ 1 - u) :
    a ^ N ≤ Real.exp (-((N : ℝ) * u)) := by sorry
