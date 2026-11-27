-- Prove2me | Theorems.Thm_SizeRamsey_Plan_compGraph_degree
-- name    : SizeRamsey.Plan.compGraph_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:20:17.309564+00:00
-- url     : https://prove2.me/theorems/058f35d8-a6af-41e1-8b61-65d2f0e13679
-- title:
--   Plan: comp Graph degree
-- statement:
--   The Plan construction uses the comp Graph degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Components.lean#L90-L94
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Components.lean#L90-L94

module
public import Definitions.Def_SizeRamsey_Deletion
public import Definitions.Def_SizeRamsey_Components
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem SizeRamsey.Plan.compGraph_degree
    (C : G.ConnectedComponent) (v : C.supp) :
    (compGraph G C).degree v = G.degree v.val := by sorry
