-- Prove2me | Theorems.Thm_SizeRamsey_Plan_tau4_erase_lift
-- name    : SizeRamsey.Plan.tau4_erase_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:19:56.951806+00:00
-- url     : https://prove2.me/theorems/08a817c5-fa88-444c-8561-dfdd37fe0f77
-- title:
--   Plan: tau4 erase lift
-- statement:
--   The Plan construction uses the tau4 erase lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L188-L204
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L188-L204

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

theorem SizeRamsey.Plan.tau4_erase_lift
    (D X : Finset V) (hX : X ⊆ D)
    (hHit : HitsDeleted G D X)
    (T : Finset {v : V // v ∉ D})
    (hT : c4Transversal (erase G D) T) :
    c4Transversal G (liftTransversal D X T) ∧
      (liftTransversal D X T).card ≤ T.card + X.card := by sorry
