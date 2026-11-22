-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_annulusMean_le_fullWeightedMean
-- name    : PebblingLean.Hypercube.annulusMean_le_fullWeightedMean
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:52:02.449043+00:00
-- url     : https://prove2.me/theorems/92efebfb-4d36-47c2-9cb4-3279341084ba
-- title:
--   Hypercube: annulus Mean le full Weighted Mean
-- statement:
--   Truncating to an annulus can only decrease the full weighted expectation
--   `2^rOut (3/4)^n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L292-L351
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L292-L351

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

theorem PebblingLean.Hypercube.annulusMean_le_fullWeightedMean (n rIn rOut : ℕ) :
    (annulusMean n rIn rOut : ℝ) ≤
      (2 ^ rOut : ℝ) * (((3 : ℝ) / 4) ^ n) := by sorry
