-- Prove2me | Theorems.Thm_PebblingLean_FiniteProbability_uniformProbability_exists_le_sum
-- name    : PebblingLean.FiniteProbability.uniformProbability_exists_le_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:09.913497+00:00
-- url     : https://prove2.me/theorems/222b2283-382c-43dc-abd7-72741ffbad2f
-- title:
--   Finite Probability: uniform Probability exists le sum
-- statement:
--   Union bound for finite uniform probabilities.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/FiniteProbability.lean#L65-L91
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/FiniteProbability.lean#L65-L91

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_FiniteProbability
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.FiniteProbability
variable {Ω ι : Type*}

theorem PebblingLean.FiniteProbability.uniformProbability_exists_le_sum [Fintype Ω] [Nonempty Ω]
    [Fintype ι] (P : ι → Ω → Prop)
    [∀ i, DecidablePred (P i)]
    [DecidablePred fun ω => ∃ i : ι, P i ω] :
    uniformProbability (fun ω : Ω => ∃ i : ι, P i ω) ≤
      ∑ i : ι, uniformProbability (P i) := by sorry
