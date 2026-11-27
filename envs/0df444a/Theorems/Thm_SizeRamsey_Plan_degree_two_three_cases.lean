-- Prove2me | Theorems.Thm_SizeRamsey_Plan_degree_two_three_cases
-- name    : SizeRamsey.Plan.degree_two_three_cases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:22:12.187965+00:00
-- url     : https://prove2.me/theorems/ab82f362-7694-5ffe-912a-a73e1f514553
-- title:
--   Plan: degree two three cases
-- statement:
--   The Plan construction uses the degree two three cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Reductions.lean#L315-L333
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Reductions.lean#L315-L333

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

theorem SizeRamsey.Plan.degree_two_three_cases
    (hcon : G.Connected)
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3) :
    (∀ v, G.degree v = 2) ∨
    (∀ v, G.degree v = 3) ∨
    ∃ u v, G.Adj u v ∧
      G.degree u = 2 ∧ G.degree v = 3 := by sorry
