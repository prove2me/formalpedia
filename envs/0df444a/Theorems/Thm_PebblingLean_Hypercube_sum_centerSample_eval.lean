-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_sum_centerSample_eval
-- name    : PebblingLean.Hypercube.sum_centerSample_eval
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:52:11.862235+00:00
-- url     : https://prove2.me/theorems/f7e93c5a-4d0a-4649-ac77-d0189157a74c
-- title:
--   Hypercube: sum center Sample eval
-- statement:
--   For a fixed coordinate of the random center tuple, summing over all samples
--   is the one-center sum multiplied by the number of choices for the remaining
--   coordinates.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L736-L794
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L736-L794

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

theorem PebblingLean.Hypercube.sum_centerSample_eval {n N : ℕ} (j : Fin N)
    (f : HypercubeVertex n → ℕ) :
    (∑ sample : CenterSample n N, (f (sample j) : ℚ)) =
      ((2 ^ n) ^ (N - 1) : ℚ) *
        ∑ center : HypercubeVertex n, (f center : ℚ) := by sorry
