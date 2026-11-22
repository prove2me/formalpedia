-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_sampleContributionSecondMomentProxy_le_two_width_mul_T
-- name    : PebblingLean.Hypercube.sampleContributionSecondMomentProxy_le_two_width_mul_T
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:53:40.872148+00:00
-- url     : https://prove2.me/theorems/fe1471a6-229b-478f-89b2-c44828895f77
-- title:
--   Hypercube: sample Contribution Second Moment Proxy le two width mul T
-- statement:
--   Paper-facing variance-proxy corollary: once the expected total contribution
--   is at most `2T`, the Bernstein variance proxy is at most `2 B_0 T`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L881-L896
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L881-L896

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

theorem PebblingLean.Hypercube.sampleContributionSecondMomentProxy_le_two_width_mul_T
    {n N rIn rOut T : ℕ} (target : HypercubeVertex n)
    (hmean_upper :
      sampleContributionExpectation (N := N) rIn rOut target ≤ 2 * (T : ℚ)) :
    sampleContributionSecondMomentProxy (N := N) rIn rOut target ≤
      2 * (2 ^ (rOut - rIn) : ℚ) * (T : ℚ) := by sorry
