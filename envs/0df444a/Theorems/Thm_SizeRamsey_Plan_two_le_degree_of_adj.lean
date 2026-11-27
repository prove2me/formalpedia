-- Prove2me | Theorems.Thm_SizeRamsey_Plan_two_le_degree_of_adj
-- name    : SizeRamsey.Plan.two_le_degree_of_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:20:44.542363+00:00
-- url     : https://prove2.me/theorems/01e98ce5-85b2-5522-ad0b-4e28267f5754
-- title:
--   Plan: two le degree of adj
-- statement:
--   The Plan construction uses the two le degree of adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Reductions.lean#L35-L38
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Reductions.lean#L35-L38

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

theorem SizeRamsey.Plan.two_le_degree_of_adj {x a b : V} (ha : G.Adj x a) (hb : G.Adj x b) (hab : a ≠ b) :
    2 ≤ G.degree x := by sorry
