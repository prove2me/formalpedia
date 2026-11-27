-- Prove2me | Theorems.Thm_SizeRamsey_Plan_universal
-- name    : SizeRamsey.Plan.universal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:20:50.149429+00:00
-- url     : https://prove2.me/theorems/b054b927-5632-49a6-9918-26990ffbb550
-- title:
--   Plan: universal
-- statement:
--   The Plan construction uses the universal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Universal.lean#L23-L117
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Universal.lean#L23-L117

module
public import Definitions.Def_SizeRamsey_Reductions
public import Definitions.Def_SizeRamsey_Universal
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable

theorem SizeRamsey.Plan.universal
    {V : Type u} [Fintype V] (G : SimpleGraph V) :
    4 * tau4 G ≤ edgeCount G := by sorry
