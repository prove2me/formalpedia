-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_targetLowerTailExponentialMoment_eq
-- name    : PebblingLean.Hypercube.targetLowerTailExponentialMoment_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:51:12.654536+00:00
-- url     : https://prove2.me/theorems/f5790b69-419e-4a10-85ed-c95ab0958b06
-- title:
--   Hypercube: target Lower Tail Exponential Moment eq
-- statement:
--   Independence factorization for the lower-tail exponential moment.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1241-L1280
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1241-L1280

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

theorem PebblingLean.Hypercube.targetLowerTailExponentialMoment_eq
    {n N rIn rOut T : ℕ} (target : HypercubeVertex n) (lam : ℝ) :
    targetLowerTailExponentialMoment (N := N) rIn rOut T target lam =
      Real.exp (lam * (T : ℝ)) *
        (oneCenterNegativeExponentialMoment rIn rOut target lam) ^ N := by sorry
