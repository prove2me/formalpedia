-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_oneCenterNegativeExponentialMoment_le_chord
-- name    : PebblingLean.Hypercube.oneCenterNegativeExponentialMoment_le_chord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:52:21.7088+00:00
-- url     : https://prove2.me/theorems/e79dcb21-4085-4132-9ea0-b15cbbfff671
-- title:
--   Hypercube: one Center Negative Exponential Moment le chord
-- statement:
--   One-center bounded-nonnegative Chernoff estimate: the negative exponential
--   moment is bounded by the chord estimate in terms of the one-center mean and
--   the annulus width `B_0 = 2^(rOut-rIn)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L978-L1033
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L978-L1033

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

theorem PebblingLean.Hypercube.oneCenterNegativeExponentialMoment_le_chord {n rIn rOut : ℕ}
    (target : HypercubeVertex n) (lam : ℝ) :
    oneCenterNegativeExponentialMoment rIn rOut target lam ≤
      1 - (1 - Real.exp (-(lam * (2 ^ (rOut - rIn) : ℝ)))) *
        (oneCenterContributionExpectationReal rIn rOut target /
          (2 ^ (rOut - rIn) : ℝ)) := by sorry
