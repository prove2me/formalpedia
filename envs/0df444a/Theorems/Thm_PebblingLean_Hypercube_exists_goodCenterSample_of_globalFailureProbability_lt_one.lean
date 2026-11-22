-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_exists_goodCenterSample_of_globalFailureProbability_lt_one
-- name    : PebblingLean.Hypercube.exists_goodCenterSample_of_globalFailureProbability_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:51:06.032727+00:00
-- url     : https://prove2.me/theorems/2641dc4a-5a90-470d-bc45-b5f807ef20cb
-- title:
--   Hypercube: exists good Center Sample of global Failure Probability lt one
-- statement:
--   Probabilistic-method extraction: if the probability that some target fails
--   is less than one, then a good center sample exists.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1589-L1608
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L1589-L1608

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

theorem PebblingLean.Hypercube.exists_goodCenterSample_of_globalFailureProbability_lt_one {n N rIn rOut T : ℕ}
    (hprob : globalFailureProbability (n := n) (N := N) rIn rOut T < 1) :
    ∃ sample : CenterSample n N,
      IsGoodCenterList n rIn rOut T sample.toList := by sorry
