-- Prove2me | Theorems.Thm_SizeRamsey_Plan_square_component_reduction
-- name    : SizeRamsey.Plan.square_component_reduction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:24:17.090603+00:00
-- url     : https://prove2.me/theorems/d265426b-9cba-5dd9-8919-89b6f072533e
-- title:
--   Plan: square component reduction
-- statement:
--   The Plan construction uses the square component reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Reductions.lean#L335-L426
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Reductions.lean#L335-L426

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

theorem SizeRamsey.Plan.square_component_reduction
    (C : G.ConnectedComponent)
    (hiso : Nonempty
      (compGraph G C ≃g SimpleGraph.cycleGraph 4)) :
    tau4 G = tau4 (erase G C.supp.toFinset) + 1 ∧
    edgeCount (erase G C.supp.toFinset) + 4 =
      edgeCount G := by sorry
