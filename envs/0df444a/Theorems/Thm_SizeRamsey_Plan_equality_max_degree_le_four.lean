-- Prove2me | Theorems.Thm_SizeRamsey_Plan_equality_max_degree_le_four
-- name    : SizeRamsey.Plan.equality_max_degree_le_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:22:25.263798+00:00
-- url     : https://prove2.me/theorems/9b240041-8ddc-4b0a-b739-1212b0017471
-- title:
--   Plan: equality max degree le four
-- statement:
--   The Plan construction uses the equality max degree le four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Tightness.lean#L36-L45
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Tightness.lean#L36-L45

module
public import Definitions.Def_SizeRamsey_Universal
public import Definitions.Def_SizeRamsey_Tightness
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem SizeRamsey.Plan.equality_max_degree_le_four
    (ht : 4 * tau4 G = edgeCount G) :
    ∀ v, G.degree v ≤ 4 := by sorry
