-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_hasSolvableAtMostSize_of_bernstein_bound
-- name    : PebblingLean.Hypercube.hasSolvableAtMostSize_of_bernstein_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:51:14.25546+00:00
-- url     : https://prove2.me/theorems/7cb9bced-aab5-426d-9840-dadedc09d7b3
-- title:
--   Hypercube: has Solvable At Most Size of bernstein bound
-- statement:
--   Costed high-demand conclusion from the Bernstein fixed-target estimate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1810-L1818
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1810-L1818

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

theorem PebblingLean.Hypercube.hasSolvableAtMostSize_of_bernstein_bound {n N rIn rOut T : ℕ} {eps : ℚ}
    (hbernstein : BernsteinTargetFailureBound n N rIn rOut T eps)
    (hunion : (Fintype.card (HypercubeVertex n) : ℚ) * eps < 1) :
    HasSolvableAtMostSize (graph n) T (N * 2 ^ rOut) := by sorry
