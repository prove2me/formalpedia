-- Prove2me | Theorems.Thm_SizeRamsey_Plan_classified_tight
-- name    : SizeRamsey.Plan.classified_tight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:37:25.984443+00:00
-- url     : https://prove2.me/theorems/802faa28-d743-43b2-ae88-57f8936d7faf
-- title:
--   Plan: classified tight
-- statement:
--   The Plan construction uses the classified tight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L158-L168
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/SmallGraphs.lean#L158-L168

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

theorem SizeRamsey.Plan.classified_tight
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (h : Classified G) :
    Tight G := by sorry
