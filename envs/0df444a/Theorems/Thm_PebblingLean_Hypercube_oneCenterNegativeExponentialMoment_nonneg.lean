-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_oneCenterNegativeExponentialMoment_nonneg
-- name    : PebblingLean.Hypercube.oneCenterNegativeExponentialMoment_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:52:21.513304+00:00
-- url     : https://prove2.me/theorems/cfd16ec8-fcd7-4207-8478-1f4c1c66bd6f
-- title:
--   Hypercube: one Center Negative Exponential Moment nonneg
-- statement:
--   The Hypercube construction uses the one Center Negative Exponential Moment nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L966-L973
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L966-L973

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

theorem PebblingLean.Hypercube.oneCenterNegativeExponentialMoment_nonneg {n rIn rOut : ℕ}
    (target : HypercubeVertex n) (lam : ℝ) :
    0 ≤ oneCenterNegativeExponentialMoment rIn rOut target lam := by sorry
