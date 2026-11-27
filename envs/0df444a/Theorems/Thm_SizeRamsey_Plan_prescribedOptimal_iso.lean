-- Prove2me | Theorems.Thm_SizeRamsey_Plan_prescribedOptimal_iso
-- name    : SizeRamsey.Plan.prescribedOptimal_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:23:38.567923+00:00
-- url     : https://prove2.me/theorems/d2c92dee-3bf3-5124-9336-09633bfee5fc
-- title:
--   Plan: prescribed Optimal iso
-- statement:
--   The Plan construction uses the prescribed Optimal iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L147-L156
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L147-L156

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable

theorem SizeRamsey.Plan.prescribedOptimal_iso
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (h : PrescribedOptimal H) :
    PrescribedOptimal G := by sorry
