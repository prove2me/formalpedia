-- Prove2me | Theorems.Thm_PerfectGraph_exists_indepSet_card_eq_indepNum_induce
-- name    : PerfectGraph.exists_indepSet_card_eq_indepNum_induce
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:27:50.274207+00:00
-- url     : https://prove2.me/theorems/50347ca7-f437-4c59-bd6a-928df38f5697
-- title:
--   Perfect Graph: exists indep Set card eq indep Num induce
-- statement:
--   The Perfect Graph construction uses the exists indep Set card eq indep Num induce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Gasparian.lean#L97-L100
-- source:
--   https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Gasparian.lean#L97-L100

module
public import Mathlib
public import Definitions.Def_PerfectLib_Gasparian
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open PerfectGraph
variable {V : Type*} (G : SimpleGraph V)

theorem PerfectGraph.exists_indepSet_card_eq_indepNum_induce (S : Finset V) :
    ∃ K ⊆ S, G.IsIndepSet (K : Set V) ∧ K.card = (G.induce (S : Set V)).indepNum := by sorry
