-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_annulusMean_eq_fullWeightedMean_mul_binomialWindowProbThird
-- name    : PebblingLean.Hypercube.annulusMean_eq_fullWeightedMean_mul_binomialWindowProbThird
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:52:02.361634+00:00
-- url     : https://prove2.me/theorems/78043661-ea6b-4bf8-bd90-77808d04cd9e
-- title:
--   Hypercube: annulus Mean eq full Weighted Mean mul binomial Window Prob Third
-- statement:
--   Exact normalization of the annulus mean: it is the full weighted mean
--   `2^rOut (3/4)^n` times a `Binomial(n,1/3)` window probability.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L398-L459
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L398-L459

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

theorem PebblingLean.Hypercube.annulusMean_eq_fullWeightedMean_mul_binomialWindowProbThird
    (n rIn rOut : ℕ) :
    (annulusMean n rIn rOut : ℝ) =
      (2 ^ rOut : ℝ) * (((3 : ℝ) / 4) ^ n) *
        binomialWindowProbThird n rIn rOut := by sorry
