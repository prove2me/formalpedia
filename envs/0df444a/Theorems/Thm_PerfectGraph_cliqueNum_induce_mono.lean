-- Prove2me | Theorems.Thm_PerfectGraph_cliqueNum_induce_mono
-- name    : PerfectGraph.cliqueNum_induce_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:28:01.37483+00:00
-- url     : https://prove2.me/theorems/1c4f058b-fea4-4ea2-a897-b90d22d78688
-- title:
--   Perfect Graph: clique Num induce mono
-- statement:
--   The Perfect Graph construction uses the clique Num induce mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Gasparian.lean#L102-L106
-- source:
--   https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Gasparian.lean#L102-L106

module
public import Mathlib
public import Definitions.Def_PerfectLib_Gasparian
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open PerfectGraph
variable {V : Type*} (G : SimpleGraph V)

theorem PerfectGraph.cliqueNum_induce_mono [Finite V] {S T : Finset V} (h : T ⊆ S) :
    (G.induce (T : Set V)).cliqueNum ≤ (G.induce (S : Set V)).cliqueNum := by sorry
