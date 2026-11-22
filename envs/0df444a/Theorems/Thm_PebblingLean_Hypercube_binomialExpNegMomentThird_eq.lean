-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_binomialExpNegMomentThird_eq
-- name    : PebblingLean.Hypercube.binomialExpNegMomentThird_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:52:12.624818+00:00
-- url     : https://prove2.me/theorems/b851aeef-1887-4503-9d32-8e91bb5377f0
-- title:
--   Hypercube: binomial Exp Neg Moment Third eq
-- statement:
--   Exact negative exponential moment of `Binomial(n,1/3)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L542-L558
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L542-L558

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

theorem PebblingLean.Hypercube.binomialExpNegMomentThird_eq (n : ℕ) (lam : ℝ) :
    (∑ i ∈ Finset.range (n + 1),
        binomialMassThird n i * (Real.exp (-lam)) ^ i) =
      (((1 : ℝ) / 3) * Real.exp (-lam) + ((2 : ℝ) / 3)) ^ n := by sorry
