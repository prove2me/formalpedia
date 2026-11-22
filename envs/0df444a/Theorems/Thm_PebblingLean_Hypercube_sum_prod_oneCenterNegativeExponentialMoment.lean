-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_sum_prod_oneCenterNegativeExponentialMoment
-- name    : PebblingLean.Hypercube.sum_prod_oneCenterNegativeExponentialMoment
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:52:25.431454+00:00
-- url     : https://prove2.me/theorems/80e71215-b388-46af-bc49-509f7114bf55
-- title:
--   Hypercube: sum prod one Center Negative Exponential Moment
-- statement:
--   The product-space sum of independent one-center exponential factors
--   factors as the `N`th power of the one-center sum.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1185-L1199
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1185-L1199

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

theorem PebblingLean.Hypercube.sum_prod_oneCenterNegativeExponentialMoment {n N rIn rOut : ℕ}
    (target : HypercubeVertex n) (lam : ℝ) :
    (∑ sample : CenterSample n N,
      ∏ j : Fin N,
        Real.exp (-(lam *
          (annulusContribution rIn rOut target (sample j) : ℝ)))) =
      (∑ center : HypercubeVertex n,
        Real.exp (-(lam *
          (annulusContribution rIn rOut target center : ℝ)))) ^ N := by sorry
