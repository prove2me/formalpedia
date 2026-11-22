-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_chernoffMeanLowerBound_iff_annulusMean
-- name    : PebblingLean.Hypercube.chernoffMeanLowerBound_iff_annulusMean
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:52:38.891666+00:00
-- url     : https://prove2.me/theorems/db1d65c8-ee88-4b43-972f-757a9b048f9a
-- title:
--   Hypercube: chernoff Mean Lower Bound iff annulus Mean
-- statement:
--   The Hypercube construction uses the chernoff Mean Lower Bound iff annulus Mean property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1638-L1646
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1638-L1646

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

theorem PebblingLean.Hypercube.chernoffMeanLowerBound_iff_annulusMean {n N rIn rOut T : ℕ} :
    ChernoffMeanLowerBound n N rIn rOut T ↔
      (T : ℚ) ≤ (N : ℚ) * annulusMean n rIn rOut := by sorry
