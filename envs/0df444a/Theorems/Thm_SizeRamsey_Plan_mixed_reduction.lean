-- Prove2me | Theorems.Thm_SizeRamsey_Plan_mixed_reduction
-- name    : SizeRamsey.Plan.mixed_reduction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:22:07.61214+00:00
-- url     : https://prove2.me/theorems/4b656c35-99ab-571f-8d2b-27a302b9cb57
-- title:
--   Plan: mixed reduction
-- statement:
--   The Plan construction uses the mixed reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Reductions.lean#L102-L131
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Reductions.lean#L102-L131

module
public import Definitions.Def_SizeRamsey_Components
public import Definitions.Def_SizeRamsey_SmallGraphs
public import Definitions.Def_SizeRamsey_Reductions
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem SizeRamsey.Plan.mixed_reduction
    {u v : V} (h : G.Adj u v)
    (hu : G.degree u = 2) (hv : G.degree v = 3) :
    tau4 G ≤ tau4 (erase G {u,v}) + 1 ∧
    edgeCount (erase G {u,v}) + 4 = edgeCount G := by sorry
