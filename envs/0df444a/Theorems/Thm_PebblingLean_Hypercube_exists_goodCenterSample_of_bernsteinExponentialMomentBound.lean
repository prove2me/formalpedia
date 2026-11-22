-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_exists_goodCenterSample_of_bernsteinExponentialMomentBound
-- name    : PebblingLean.Hypercube.exists_goodCenterSample_of_bernsteinExponentialMomentBound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:52:51.229189+00:00
-- url     : https://prove2.me/theorems/e981a45b-4d3e-4478-91c0-1d16b47a26dd
-- title:
--   Hypercube: exists good Center Sample of bernstein Exponential Moment Bound
-- statement:
--   The Hypercube construction uses the exists good Center Sample of bernstein Exponential Moment Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L2022-L2030
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L2022-L2030

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

theorem PebblingLean.Hypercube.exists_goodCenterSample_of_bernsteinExponentialMomentBound
    {n N rIn rOut T : ℕ} {variance scale gap : ℝ} {eps : ℚ}
    (hmoment : BernsteinExponentialMomentBound n N rIn rOut T variance scale gap)
    (hexp : Real.exp (-(bernsteinExponent variance scale gap)) ≤ (eps : ℝ))
    (hunion : (Fintype.card (HypercubeVertex n) : ℚ) * eps < 1) :
    ∃ sample : CenterSample n N,
      IsGoodCenterList n rIn rOut T sample.toList := by sorry
