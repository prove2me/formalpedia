-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_exists_goodCenterSample_of_bernstein_bound
-- name    : PebblingLean.Hypercube.exists_goodCenterSample_of_bernstein_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:51:09.527704+00:00
-- url     : https://prove2.me/theorems/59ec8f33-fa0c-4f3e-a01c-50b9f11a4c1b
-- title:
--   Hypercube: exists good Center Sample of bernstein bound
-- statement:
--   The usual union-bound finish from a Bernstein fixed-target estimate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1787-L1807
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1787-L1807

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

theorem PebblingLean.Hypercube.exists_goodCenterSample_of_bernstein_bound {n N rIn rOut T : ℕ} {eps : ℚ}
    (hbernstein : BernsteinTargetFailureBound n N rIn rOut T eps)
    (hunion : (Fintype.card (HypercubeVertex n) : ℚ) * eps < 1) :
    ∃ sample : CenterSample n N,
      IsGoodCenterList n rIn rOut T sample.toList := by sorry
