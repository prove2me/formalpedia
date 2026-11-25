-- Prove2me | Theorems.Thm_PerfectGraph_exists_clique_card_eq_cliqueNum_induce
-- name    : PerfectGraph.exists_clique_card_eq_cliqueNum_induce
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:27:24.066182+00:00
-- url     : https://prove2.me/theorems/5eb97e32-36ca-4526-94e8-ffaacbcdc4f0
-- title:
--   Perfect Graph: exists clique card eq clique Num induce
-- statement:
--   The Perfect Graph construction uses the exists clique card eq clique Num induce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Gasparian.lean#L66-L81
-- source:
--   https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Gasparian.lean#L66-L81

module
public import Mathlib
public import Definitions.Def_PerfectLib_Gasparian
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open PerfectGraph
variable {V : Type*} (G : SimpleGraph V)

theorem PerfectGraph.exists_clique_card_eq_cliqueNum_induce (S : Finset V) :
    ∃ K ⊆ S, G.IsClique (K : Set V) ∧ K.card = (G.induce (S : Set V)).cliqueNum := by sorry
