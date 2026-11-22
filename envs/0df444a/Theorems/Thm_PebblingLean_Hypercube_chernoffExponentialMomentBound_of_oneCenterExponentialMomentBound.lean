-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_chernoffExponentialMomentBound_of_oneCenterExponentialMomentBound
-- name    : PebblingLean.Hypercube.chernoffExponentialMomentBound_of_oneCenterExponentialMomentBound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:52:39.567806+00:00
-- url     : https://prove2.me/theorems/620c7355-0632-4486-b99a-2378c5091e5a
-- title:
--   Hypercube: chernoff Exponential Moment Bound of one Center Exponential Moment Bound
-- statement:
--   The Hypercube construction uses the chernoff Exponential Moment Bound of one Center Exponential Moment Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1702-L1712
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1702-L1712

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

theorem PebblingLean.Hypercube.chernoffExponentialMomentBound_of_oneCenterExponentialMomentBound
    {n N rIn rOut T : ℕ} {lam eps : ℝ}
    (hbound : OneCenterExponentialMomentBound n N rIn rOut T lam eps) :
    ChernoffExponentialMomentBound n N rIn rOut T eps := by sorry
