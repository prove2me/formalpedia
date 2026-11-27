-- Prove2me | Theorems.Thm_SizeRamsey_Plan_octahedron_avoid_pair
-- name    : SizeRamsey.Plan.octahedron_avoid_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:23:22.927895+00:00
-- url     : https://prove2.me/theorems/d1f33e01-466b-5f05-81eb-a4bf24147dd4
-- title:
--   Plan: octahedron avoid pair
-- statement:
--   The Plan construction uses the octahedron avoid pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L73-L76
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L73-L76

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v

theorem SizeRamsey.Plan.octahedron_avoid_pair : ∀ x y : Fin 6, ∃ a b c d : Fin 6, octahedron.Adj a b ∧
    octahedron.Adj b c ∧ octahedron.Adj c d ∧ octahedron.Adj d a ∧ a ≠ c ∧ b ≠ d ∧
    a ≠ x ∧ b ≠ x ∧ c ≠ x ∧ d ≠ x ∧ a ≠ y ∧ b ≠ y ∧ c ≠ y ∧ d ≠ y := by sorry
