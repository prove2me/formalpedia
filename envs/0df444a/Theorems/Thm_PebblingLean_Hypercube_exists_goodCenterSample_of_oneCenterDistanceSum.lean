-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_exists_goodCenterSample_of_oneCenterDistanceSum
-- name    : PebblingLean.Hypercube.exists_goodCenterSample_of_oneCenterDistanceSum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:54:20.078679+00:00
-- url     : https://prove2.me/theorems/051bbd40-7786-49ff-b4a7-6af366d1622e
-- title:
--   Hypercube: exists good Center Sample of one Center Distance Sum
-- statement:
--   The Hypercube construction uses the exists good Center Sample of one Center Distance Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L2041-L2051
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L2041-L2051

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

theorem PebblingLean.Hypercube.exists_goodCenterSample_of_oneCenterDistanceSum
    {n N rIn rOut T : ℕ} {lam variance scale gap : ℝ} {eps : ℚ}
    (hbound :
      OneCenterDistanceSumExponentialMomentBound n N rIn rOut T lam
        (Real.exp (-(bernsteinExponent variance scale gap))))
    (hexp : Real.exp (-(bernsteinExponent variance scale gap)) ≤ (eps : ℝ))
    (hunion : (Fintype.card (HypercubeVertex n) : ℚ) * eps < 1) :
    ∃ sample : CenterSample n N,
      IsGoodCenterList n rIn rOut T sample.toList := by sorry
