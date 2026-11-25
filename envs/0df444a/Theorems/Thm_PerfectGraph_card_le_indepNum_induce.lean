-- Prove2me | Theorems.Thm_PerfectGraph_card_le_indepNum_induce
-- name    : PerfectGraph.card_le_indepNum_induce
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:28:05.186271+00:00
-- url     : https://prove2.me/theorems/0b6fc1a6-08df-4490-9182-a43740603183
-- title:
--   Perfect Graph: card le indep Num induce
-- statement:
--   The Perfect Graph construction uses the card le indep Num induce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Gasparian.lean#L91-L95
-- source:
--   https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Gasparian.lean#L91-L95

module
public import Mathlib
public import Definitions.Def_PerfectLib_Gasparian
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open PerfectGraph
variable {V : Type*} (G : SimpleGraph V)

theorem PerfectGraph.card_le_indepNum_induce [Finite V] {S K : Finset V} (hKS : K ⊆ S)
    (hK : G.IsIndepSet (K : Set V)) :
    K.card ≤ (G.induce (S : Set V)).indepNum := by sorry
