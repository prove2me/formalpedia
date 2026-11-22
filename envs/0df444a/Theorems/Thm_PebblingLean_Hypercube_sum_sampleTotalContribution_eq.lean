-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_sum_sampleTotalContribution_eq
-- name    : PebblingLean.Hypercube.sum_sampleTotalContribution_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:52:11.163802+00:00
-- url     : https://prove2.me/theorems/c7df8306-ef02-4bb5-a658-fca1c6c77df2
-- title:
--   Hypercube: sum sample Total Contribution eq
-- statement:
--   Numerator of the `N`-center expectation, written as `N` copies of the
--   one-coordinate sum.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L798-L829
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L798-L829

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

theorem PebblingLean.Hypercube.sum_sampleTotalContribution_eq {n N rIn rOut : ℕ}
    (target : HypercubeVertex n) :
    (∑ sample : CenterSample n N,
        (sampleTotalContribution rIn rOut target sample : ℚ)) =
      (N : ℚ) * ((2 ^ n) ^ (N - 1) : ℚ) *
        ∑ center : HypercubeVertex n,
          (annulusContribution rIn rOut target center : ℚ) := by sorry
