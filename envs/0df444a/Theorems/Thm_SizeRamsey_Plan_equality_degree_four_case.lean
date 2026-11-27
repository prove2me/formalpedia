-- Prove2me | Theorems.Thm_SizeRamsey_Plan_equality_degree_four_case
-- name    : SizeRamsey.Plan.equality_degree_four_case
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:24:42.829784+00:00
-- url     : https://prove2.me/theorems/8ac6a07f-819e-46b9-a9d8-b8a5a752adf5
-- title:
--   Plan: equality degree four case
-- statement:
--   The Plan construction uses the equality degree four case property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Equality/DegreeFour.lean#L356-L391
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Equality/DegreeFour.lean#L356-L391

module
public import Definitions.Def_SizeRamsey_Equality_Common
public import Definitions.Def_SizeRamsey_Equality_Extension
public import Definitions.Def_SizeRamsey_Equality_DegreeFour
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
universe u
attribute [local instance] Classical.propDecidable

theorem SizeRamsey.Plan.equality_degree_four_case
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hc : G.Connected)
    (hp : 0 < edgeCount G)
    (hm : edgeCount G ≤ 16)
    (ht : Tight G)
    (ih : SmallerClassified G)
    (h4 : ∃ v, G.degree v = 4) :
    Classified G := by sorry
