-- Prove2me | Theorems.Thm_SizeRamsey_Plan_erase_degree
-- name    : SizeRamsey.Plan.erase_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:21:53.204851+00:00
-- url     : https://prove2.me/theorems/ff396514-29d7-41dc-9837-67af7c4b1f97
-- title:
--   Plan: erase degree
-- statement:
--   The Plan construction uses the erase degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L293-L298
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L293-L298

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
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem SizeRamsey.Plan.erase_degree
    (D : Finset V) (v : {x : V // x ∉ D}) :
    (erase G D).degree v +
      (G.neighborFinset v.val ∩ D).card = G.degree v.val := by sorry
