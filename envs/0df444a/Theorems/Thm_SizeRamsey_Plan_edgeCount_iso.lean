-- Prove2me | Theorems.Thm_SizeRamsey_Plan_edgeCount_iso
-- name    : SizeRamsey.Plan.edgeCount_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:19:19.157345+00:00
-- url     : https://prove2.me/theorems/01d7c695-efeb-41ff-94e3-0ec563553333
-- title:
--   Plan: edge Count iso
-- statement:
--   The Plan construction uses the edge Count iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Basic.lean#L105-L110
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Basic.lean#L105-L110

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

theorem SizeRamsey.Plan.edgeCount_iso
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    edgeCount G = edgeCount H := by sorry
