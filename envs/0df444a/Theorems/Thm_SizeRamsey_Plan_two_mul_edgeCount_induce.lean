-- Prove2me | Theorems.Thm_SizeRamsey_Plan_two_mul_edgeCount_induce
-- name    : SizeRamsey.Plan.two_mul_edgeCount_induce
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:20:25.211753+00:00
-- url     : https://prove2.me/theorems/fc3d56cc-ad0e-55e8-a692-232e81027f97
-- title:
--   Plan: two mul edge Count induce
-- statement:
--   The Plan construction uses the two mul edge Count induce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Reductions.lean#L54-L62
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Reductions.lean#L54-L62

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

theorem SizeRamsey.Plan.two_mul_edgeCount_induce (D : Finset V) :
    2 * edgeCount (G.induce (D : Set V)) =
      ∑ x ∈ D, ∑ y ∈ D, if G.Adj x y then 1 else 0 := by sorry
