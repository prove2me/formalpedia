-- Prove2me | Theorems.Thm_PebblingLean_FiniteProbability_exp_neg_le_inv_two_pow_succ_of_log_le
-- name    : PebblingLean.FiniteProbability.exp_neg_le_inv_two_pow_succ_of_log_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:37.564043+00:00
-- url     : https://prove2.me/theorems/528b576e-5b26-4330-8718-7bd781b0cafa
-- title:
--   Finite Probability: exp neg le inv two pow succ of log le
-- statement:
--   A convenient way to discharge the hypercube union bound: an exponent at
--   least `(n+1) log 2` makes the fixed-target failure probability at most
--   `2^-(n+1)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Concentration.lean#L224-L243
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Concentration.lean#L224-L243

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

theorem PebblingLean.FiniteProbability.exp_neg_le_inv_two_pow_succ_of_log_le (n : ℕ) {exponent : ℝ}
    (hlog : ((n + 1 : ℕ) : ℝ) * Real.log 2 ≤ exponent) :
    Real.exp (-exponent) ≤
      (((1 : ℚ) / (2 ^ (n + 1) : ℚ) : ℚ) : ℝ) := by sorry
