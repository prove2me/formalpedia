-- Prove2me | Theorems.Thm_SizeRamsey_Plan_equality_two_regular_case
-- name    : SizeRamsey.Plan.equality_two_regular_case
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:24:43.612839+00:00
-- url     : https://prove2.me/theorems/0ee1b13b-5fd1-5651-953f-1dfe9e87bfc8
-- title:
--   Plan: equality two regular case
-- statement:
--   The Plan construction uses the equality two regular case property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Equality/TwoRegular.lean#L20-L27
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Equality/TwoRegular.lean#L20-L27

module
public import Definitions.Def_SizeRamsey_AInterface
public import Definitions.Def_SizeRamsey_Equality_TwoRegular
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
universe u
attribute [local instance] Classical.propDecidable

theorem SizeRamsey.Plan.equality_two_regular_case
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hc : G.Connected)
    (hp : 0 < edgeCount G)
    (ht : Tight G)
    (h2 : ∀ v, G.degree v = 2) :
    Nonempty (G ≃g SimpleGraph.cycleGraph 4) := by sorry
