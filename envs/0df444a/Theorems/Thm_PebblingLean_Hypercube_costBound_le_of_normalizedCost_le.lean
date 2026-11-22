-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_costBound_le_of_normalizedCost_le
-- name    : PebblingLean.Hypercube.costBound_le_of_normalizedCost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:57:46.368391+00:00
-- url     : https://prove2.me/theorems/3852b59c-6d82-4d2b-aa49-f47d49060766
-- title:
--   Hypercube: cost Bound le of normalized Cost le
-- statement:
--   The Hypercube construction uses the cost Bound le of normalized Cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L413-L418
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L413-L418

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube

theorem PebblingLean.Hypercube.costBound_le_of_normalizedCost_le
    {costBound : ℕ → ℕ} {C : ℝ}
    (hnorm : ∀ n : ℕ, normalizedCost costBound n ≤ C) (n : ℕ) :
    (costBound n : ℝ) ≤ C * (((4 : ℝ) / 3) ^ n) := by sorry
