-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_binomialRightTailProbThird_le_chernoff
-- name    : PebblingLean.Hypercube.binomialRightTailProbThird_le_chernoff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:52:04.533164+00:00
-- url     : https://prove2.me/theorems/cb4ed511-efb3-459a-a603-eb19e857068a
-- title:
--   Hypercube: binomial Right Tail Prob Third le chernoff
-- statement:
--   Chernoff bound for the right tail of `Binomial(n,1/3)`, with arbitrary
--   nonnegative parameter `lam`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L636-L687
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L636-L687

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

theorem PebblingLean.Hypercube.binomialRightTailProbThird_le_chernoff (n rOut : ℕ) {lam : ℝ}
    (hlam : 0 ≤ lam) :
    binomialRightTailProbThird n rOut ≤
      Real.exp (-(lam * (rOut : ℝ))) *
        (((1 : ℝ) / 3) * Real.exp lam + ((2 : ℝ) / 3)) ^ n := by sorry
