-- Prove2me | Theorems.Thm_SizeRamsey_Plan_degree_ge_card_of_subset
-- name    : SizeRamsey.Plan.degree_ge_card_of_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:20:29.633114+00:00
-- url     : https://prove2.me/theorems/63f26fce-595d-43d1-a543-5439e2b36fc6
-- title:
--   Plan: degree ge card of subset
-- statement:
--   The Plan construction uses the degree ge card of subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Reductions.lean#L30-L33
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Reductions.lean#L30-L33

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

theorem SizeRamsey.Plan.degree_ge_card_of_subset (x : V) (s : Finset V) (hs : ∀ y ∈ s, G.Adj x y) :
    s.card ≤ G.degree x := by sorry
