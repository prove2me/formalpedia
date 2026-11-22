-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_card_filter_dist_eq
-- name    : PebblingLean.Hypercube.card_filter_dist_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:51:10.563811+00:00
-- url     : https://prove2.me/theorems/f8271eb2-967b-46b5-9cb6-a265ed91c641
-- title:
--   Hypercube: card filter dist eq
-- statement:
--   Cardinality of a Hamming sphere, written as a filtered finite sum.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L133-L142
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L133-L142

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

theorem PebblingLean.Hypercube.card_filter_dist_eq {n i : ℕ} (target : HypercubeVertex n) :
    (Finset.univ.filter fun center : HypercubeVertex n => dist target center = i).card =
      Nat.choose n i := by sorry
