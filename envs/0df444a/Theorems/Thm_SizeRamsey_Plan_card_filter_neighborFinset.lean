-- Prove2me | Theorems.Thm_SizeRamsey_Plan_card_filter_neighborFinset
-- name    : SizeRamsey.Plan.card_filter_neighborFinset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:19:14.696856+00:00
-- url     : https://prove2.me/theorems/2b389e44-2080-4327-a2ad-85057844b0ab
-- title:
--   Plan: card filter neighbor Finset
-- statement:
--   The Plan construction uses the card filter neighbor Finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L152-L158
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Deletion.lean#L152-L158

module
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_Deletion
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem SizeRamsey.Plan.card_filter_neighborFinset (v : V) (p : V → Prop) [DecidablePred p] :
    ((G.neighborFinset v).filter p).card =
      ∑ w ∈ Finset.univ.filter p, if G.Adj v w then 1 else 0 := by sorry
