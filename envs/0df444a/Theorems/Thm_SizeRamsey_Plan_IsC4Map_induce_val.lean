-- Prove2me | Theorems.Thm_SizeRamsey_Plan_IsC4Map_induce_val
-- name    : SizeRamsey.Plan.IsC4Map.induce_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:40.451799+00:00
-- url     : https://prove2.me/theorems/0befb5e5-0ea3-5afe-9dc8-c6a8d55a207f
-- title:
--   Is C4 Map: induce val
-- statement:
--   The Is C4 Map construction uses the induce val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L60-L63
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L60-L63

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
variable {V : Type*} {W : Type*}

theorem SizeRamsey.Plan.IsC4Map.induce_val {G : SimpleGraph V} {s : Set V} {f : Fin 4 → s}
    (hf : IsC4Map (G.induce s) f) : IsC4Map G (fun i => (f i : V)) := by sorry
