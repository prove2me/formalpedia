-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_binomialExpMomentThird_eq
-- name    : PebblingLean.Hypercube.binomialExpMomentThird_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:52:03.881528+00:00
-- url     : https://prove2.me/theorems/250195b5-4922-43ef-b736-1a18e0cf1fe4
-- title:
--   Hypercube: binomial Exp Moment Third eq
-- statement:
--   Exact positive exponential moment of `Binomial(n,1/3)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L561-L577
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L561-L577

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

theorem PebblingLean.Hypercube.binomialExpMomentThird_eq (n : ℕ) (lam : ℝ) :
    (∑ i ∈ Finset.range (n + 1),
        binomialMassThird n i * (Real.exp lam) ^ i) =
      (((1 : ℝ) / 3) * Real.exp lam + ((2 : ℝ) / 3)) ^ n := by sorry
