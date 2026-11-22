-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_card_centerSample
-- name    : PebblingLean.Hypercube.card_centerSample
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:53:13.103748+00:00
-- url     : https://prove2.me/theorems/bc014034-40f8-469a-ad36-e51b7efa634e
-- title:
--   Hypercube: card center Sample
-- statement:
--   The Hypercube construction uses the card center Sample property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L56-L58
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L56-L58

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

theorem PebblingLean.Hypercube.card_centerSample (n N : ℕ) :
    Fintype.card (CenterSample n N) = (2 ^ n) ^ N := by sorry
