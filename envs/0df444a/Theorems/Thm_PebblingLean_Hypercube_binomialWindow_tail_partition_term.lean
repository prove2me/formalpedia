-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_binomialWindow_tail_partition_term
-- name    : PebblingLean.Hypercube.binomialWindow_tail_partition_term
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:52:10.283777+00:00
-- url     : https://prove2.me/theorems/7e18f8cd-d4ee-42f2-94d7-4fcb70db0152
-- title:
--   Hypercube: binomial Window tail partition term
-- statement:
--   For a valid annulus, every binomial mass is either inside the window, in
--   the left tail, or in the right tail.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L497-L511
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L497-L511

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

theorem PebblingLean.Hypercube.binomialWindow_tail_partition_term {n rIn rOut i : ℕ}
    (hr : rIn ≤ rOut) :
    (if rIn ≤ i ∧ i ≤ rOut then binomialMassThird n i else 0) +
        (if i < rIn then binomialMassThird n i else 0) +
          (if rOut < i then binomialMassThird n i else 0) =
      binomialMassThird n i := by sorry
