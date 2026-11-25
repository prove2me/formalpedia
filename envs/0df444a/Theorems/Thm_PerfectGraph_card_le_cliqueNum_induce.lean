-- Prove2me | Theorems.Thm_PerfectGraph_card_le_cliqueNum_induce
-- name    : PerfectGraph.card_le_cliqueNum_induce
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:27:29.904725+00:00
-- url     : https://prove2.me/theorems/eee62336-6594-4ff4-967c-a328fcc273fd
-- title:
--   Perfect Graph: card le clique Num induce
-- statement:
--   The Perfect Graph construction uses the card le clique Num induce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Gasparian.lean#L52-L64
-- source:
--   https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Gasparian.lean#L52-L64

module
public import Mathlib
public import Definitions.Def_PerfectLib_Gasparian
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open PerfectGraph
variable {V : Type*} (G : SimpleGraph V)

theorem PerfectGraph.card_le_cliqueNum_induce [Finite V] {S K : Finset V} (hKS : K ⊆ S)
    (hK : G.IsClique (K : Set V)) :
    K.card ≤ (G.induce (S : Set V)).cliqueNum := by sorry
