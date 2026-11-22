-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_weightedSphereSum_half_eq
-- name    : PebblingLean.Hypercube.weightedSphereSum_half_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:52:01.20555+00:00
-- url     : https://prove2.me/theorems/d8215819-27f4-42b9-a2dd-e3448fdd9797
-- title:
--   Hypercube: weighted Sphere Sum half eq
-- statement:
--   Binomial evaluation of the full weighted Hamming-sphere sum.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L257-L269
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L257-L269

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

theorem PebblingLean.Hypercube.weightedSphereSum_half_eq (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℝ) * ((1 : ℝ) / 2) ^ i) =
      ((3 : ℝ) / 2) ^ n := by sorry
