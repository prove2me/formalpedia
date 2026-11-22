-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_sum_filter_dist_eq_annulusContribution
-- name    : PebblingLean.Hypercube.sum_filter_dist_eq_annulusContribution
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:51:47.859683+00:00
-- url     : https://prove2.me/theorems/599fbe87-655f-44f1-b169-13fa0dff2893
-- title:
--   Hypercube: sum filter dist eq annulus Contribution
-- statement:
--   Sum of the annulus contribution over one Hamming sphere.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L145-L185
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L145-L185

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

theorem PebblingLean.Hypercube.sum_filter_dist_eq_annulusContribution {n rIn rOut i : ℕ}
    (target : HypercubeVertex n) :
    (∑ center ∈
        (Finset.univ.filter fun center : HypercubeVertex n => dist target center = i),
        annulusContribution rIn rOut target center) =
      Nat.choose n i *
        if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 := by sorry
