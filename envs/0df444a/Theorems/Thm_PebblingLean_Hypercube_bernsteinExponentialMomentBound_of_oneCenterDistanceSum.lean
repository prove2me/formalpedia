-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_bernsteinExponentialMomentBound_of_oneCenterDistanceSum
-- name    : PebblingLean.Hypercube.bernsteinExponentialMomentBound_of_oneCenterDistanceSum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:51:15.711102+00:00
-- url     : https://prove2.me/theorems/267bdb42-2aeb-4590-a8c9-183d8025275c
-- title:
--   Hypercube: bernstein Exponential Moment Bound of one Center Distance Sum
-- statement:
--   The Hypercube construction uses the bernstein Exponential Moment Bound of one Center Distance Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1770-L1777
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1770-L1777

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

theorem PebblingLean.Hypercube.bernsteinExponentialMomentBound_of_oneCenterDistanceSum
    {n N rIn rOut T : ℕ} {lam variance scale gap : ℝ}
    (hbound :
      OneCenterDistanceSumExponentialMomentBound n N rIn rOut T lam
        (Real.exp (-(bernsteinExponent variance scale gap)))) :
    BernsteinExponentialMomentBound n N rIn rOut T variance scale gap := by sorry
