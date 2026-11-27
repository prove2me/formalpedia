-- Prove2me | Theorems.Thm_SizeRamsey_Plan_tau4_eq_of_same_squares
-- name    : SizeRamsey.Plan.tau4_eq_of_same_squares
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:55.337818+00:00
-- url     : https://prove2.me/theorems/6ef34461-0717-40ff-bd92-8bdce588a0f5
-- title:
--   Plan: tau4 eq of same squares
-- statement:
--   The Plan construction uses the tau4 eq of same squares property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L104-L107
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L104-L107

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

theorem SizeRamsey.Plan.tau4_eq_of_same_squares [Fintype V] {G H : SimpleGraph V}
    (h : ∀ f, IsC4Map G f ↔ IsC4Map H f) : tau4 G = tau4 H := by sorry
