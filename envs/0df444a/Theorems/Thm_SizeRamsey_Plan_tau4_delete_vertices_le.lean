-- Prove2me | Theorems.Thm_SizeRamsey_Plan_tau4_delete_vertices_le
-- name    : SizeRamsey.Plan.tau4_delete_vertices_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:20:03.458241+00:00
-- url     : https://prove2.me/theorems/1cf9e57e-69e5-5077-a0bf-6e0a19b03c0b
-- title:
--   Plan: tau4 delete vertices le
-- statement:
--   The Plan construction uses the tau4 delete vertices le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L206-L212
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L206-L212

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

theorem SizeRamsey.Plan.tau4_delete_vertices_le
    (D X : Finset V) (hX : X ⊆ D)
    (hHit : HitsDeleted G D X) :
    tau4 G ≤ tau4 (erase G D) + X.card := by sorry
