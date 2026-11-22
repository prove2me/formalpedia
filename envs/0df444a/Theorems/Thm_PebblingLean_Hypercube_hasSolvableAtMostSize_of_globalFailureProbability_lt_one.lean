-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_hasSolvableAtMostSize_of_globalFailureProbability_lt_one
-- name    : PebblingLean.Hypercube.hasSolvableAtMostSize_of_globalFailureProbability_lt_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:53:53.574987+00:00
-- url     : https://prove2.me/theorems/9dd75b45-8662-4861-9fac-517098744c5b
-- title:
--   Hypercube: has Solvable At Most Size of global Failure Probability lt one
-- statement:
--   Costed high-demand conclusion from a global failure-probability bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1611-L1618
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1611-L1618

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

theorem PebblingLean.Hypercube.hasSolvableAtMostSize_of_globalFailureProbability_lt_one {n N rIn rOut T : ℕ}
    (hprob : globalFailureProbability (n := n) (N := N) rIn rOut T < 1) :
    HasSolvableAtMostSize (graph n) T (N * 2 ^ rOut) := by sorry
