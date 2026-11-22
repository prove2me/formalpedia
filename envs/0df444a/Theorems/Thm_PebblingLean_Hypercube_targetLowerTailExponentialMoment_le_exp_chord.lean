-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_targetLowerTailExponentialMoment_le_exp_chord
-- name    : PebblingLean.Hypercube.targetLowerTailExponentialMoment_le_exp_chord
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:52:31.642696+00:00
-- url     : https://prove2.me/theorems/3798f755-72cf-4692-b7f3-76d5c064b427
-- title:
--   Hypercube: target Lower Tail Exponential Moment le exp chord
-- statement:
--   Chord-based lower-tail exponential-moment bound before optimizing the
--   Chernoff parameter.  Here `B = 2^(rOut-rIn)` and the parenthesized term is the
--   one-center chord drop.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1285-L1335
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1285-L1335

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

theorem PebblingLean.Hypercube.targetLowerTailExponentialMoment_le_exp_chord
    {n N rIn rOut T : ℕ} (target : HypercubeVertex n) {lam : ℝ}
    (hlam_nonneg : 0 ≤ lam) :
    targetLowerTailExponentialMoment (N := N) rIn rOut T target lam ≤
      Real.exp
        (lam * (T : ℝ) -
          (N : ℝ) *
            ((1 - Real.exp (-(lam * (2 ^ (rOut - rIn) : ℝ)))) *
              (oneCenterContributionExpectationReal rIn rOut target /
                (2 ^ (rOut - rIn) : ℝ)))) := by sorry
