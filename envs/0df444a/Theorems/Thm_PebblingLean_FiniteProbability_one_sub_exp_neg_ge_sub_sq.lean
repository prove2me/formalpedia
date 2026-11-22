-- Prove2me | Theorems.Thm_PebblingLean_FiniteProbability_one_sub_exp_neg_ge_sub_sq
-- name    : PebblingLean.FiniteProbability.one_sub_exp_neg_ge_sub_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:28.173803+00:00
-- url     : https://prove2.me/theorems/f238a773-f292-4eba-b3d8-50096198b27a
-- title:
--   Finite Probability: one sub exp neg ge sub sq
-- statement:
--   A scalar lower bound for `1 - exp(-x)` that follows from `1 + x ≤ exp x`.
--   This is the elementary replacement for the usual Taylor estimate in the
--   bounded-nonnegative Chernoff optimization.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Concentration.lean#L160-L171
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Concentration.lean#L160-L171

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

theorem PebblingLean.FiniteProbability.one_sub_exp_neg_ge_sub_sq {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 2 ≤ 1 - Real.exp (-x) := by sorry
