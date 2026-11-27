-- Prove2me | Theorems.Thm_SizeRamsey_Plan_equality_mixed_degree_case
-- name    : SizeRamsey.Plan.equality_mixed_degree_case
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:24:32.725897+00:00
-- url     : https://prove2.me/theorems/bf6d8041-3374-5a29-8fd9-af5320561b10
-- title:
--   Plan: equality mixed degree case
-- statement:
--   The Plan construction uses the equality mixed degree case property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Equality/Mixed.lean#L165-L366
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Equality/Mixed.lean#L165-L366

module
public import Definitions.Def_SizeRamsey_Equality_Common
public import Definitions.Def_SizeRamsey_Equality_Mixed
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
universe u
attribute [local instance] Classical.propDecidable

theorem SizeRamsey.Plan.equality_mixed_degree_case
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hc : G.Connected)
    (hp : 0 < edgeCount G)
    (hm : edgeCount G ≤ 16)
    (ht : Tight G)
    (ih : SmallerClassified G)
    (hmax : ∀ v, G.degree v ≤ 3)
    (hmix : ∃ u v,
      G.Adj u v ∧ G.degree u = 2 ∧ G.degree v = 3) :
    Nonempty (G ≃g k33MinusEdge) := by sorry
