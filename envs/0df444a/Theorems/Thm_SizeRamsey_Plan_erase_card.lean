-- Prove2me | Theorems.Thm_SizeRamsey_Plan_erase_card
-- name    : SizeRamsey.Plan.erase_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:22:20.26525+00:00
-- url     : https://prove2.me/theorems/54735970-7b23-5a27-862a-d6bda31ccac7
-- title:
--   Plan: erase card
-- statement:
--   The Plan construction uses the erase card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L352-L358
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L352-L358

module
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_Deletion
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable

theorem SizeRamsey.Plan.erase_card
    {V : Type u} [Fintype V] (D : Finset V) :
    Fintype.card {x : V // x ∉ D} + D.card =
      Fintype.card V := by sorry
