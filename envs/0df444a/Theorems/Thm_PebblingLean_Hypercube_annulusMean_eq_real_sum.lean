-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_annulusMean_eq_real_sum
-- name    : PebblingLean.Hypercube.annulusMean_eq_real_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:51:12.829222+00:00
-- url     : https://prove2.me/theorems/01c1b86b-4162-46ac-ad86-cff12e86d17b
-- title:
--   Hypercube: annulus Mean eq real sum
-- statement:
--   The Hypercube construction uses the annulus Mean eq real sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L278-L288
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L278-L288

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

theorem PebblingLean.Hypercube.annulusMean_eq_real_sum (n rIn rOut : ℕ) :
    (annulusMean n rIn rOut : ℝ) =
      (∑ i ∈ Finset.range (n + 1),
        ((Nat.choose n i *
          if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ) : ℝ)) /
        (2 ^ n : ℝ) := by sorry
