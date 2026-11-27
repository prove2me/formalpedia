-- Prove2me | Theorems.Thm_SizeRamsey_Plan_small_degrees
-- name    : SizeRamsey.Plan.small_degrees
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:23:37.671361+00:00
-- url     : https://prove2.me/theorems/b67d6e6e-39e9-4ea3-aefa-74c4682f609b
-- title:
--   Plan: small degrees
-- statement:
--   The Plan construction uses the small degrees property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L137-L145
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L137-L145

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable

theorem SizeRamsey.Plan.small_degrees :
    (∀ i : Fin 4, (SimpleGraph.cycleGraph 4).degree i = 2) ∧
    (∀ i : Fin 5,
      wheel5.degree i = if i = 4 then 4 else 3) ∧
    (∀ i : Fin 6,
      k33MinusEdge.degree i =
        if i = 0 ∨ i = 3 then 2 else 3) ∧
    (∀ i : Fin 6, octahedron.degree i = 4) := by sorry
