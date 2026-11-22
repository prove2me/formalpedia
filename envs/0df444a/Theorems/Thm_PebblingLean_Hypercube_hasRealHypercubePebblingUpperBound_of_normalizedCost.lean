-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_hasRealHypercubePebblingUpperBound_of_normalizedCost
-- name    : PebblingLean.Hypercube.hasRealHypercubePebblingUpperBound_of_normalizedCost
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:57:41.785076+00:00
-- url     : https://prove2.me/theorems/cbd72860-6021-4a76-844d-5009c12a3bce
-- title:
--   Hypercube: has Real Hypercube Pebbling Upper Bound of normalized Cost
-- statement:
--   Convert an integer-valued cost-bound construction plus a real normalized
--   cost estimate into the real asymptotic upper-bound statement.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L422-L429
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L422-L429

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

theorem PebblingLean.Hypercube.hasRealHypercubePebblingUpperBound_of_normalizedCost
    {costBound : ℕ → ℕ} {C : ℝ}
    (hupper : HasHypercubePebblingUpperBound costBound)
    (hnorm : ∀ n : ℕ, normalizedCost costBound n ≤ C) :
    HasRealHypercubePebblingUpperBound C := by sorry
