-- Prove2me | Theorems.Thm_SizeRamsey_Plan_tau4_eq_zero_iff
-- name    : SizeRamsey.Plan.tau4_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:20:14.76054+00:00
-- url     : https://prove2.me/theorems/e694e45f-136c-58f9-87aa-5f728ae8e73a
-- title:
--   Plan: tau4 eq zero iff
-- statement:
--   The Plan construction uses the tau4 eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Basic.lean#L112-L124
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Basic.lean#L112-L124

module
public import Definitions.Def_SizeRamsey_Shared
public import Definitions.Def_SizeRamsey_Basic
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable

theorem SizeRamsey.Plan.tau4_eq_zero_iff
    {V : Type u} [Fintype V] (G : SimpleGraph V) :
    tau4 G = 0 ↔ ¬ HasC4 G := by sorry
