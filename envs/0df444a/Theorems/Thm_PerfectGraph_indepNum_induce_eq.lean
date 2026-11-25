-- Prove2me | Theorems.Thm_PerfectGraph_indepNum_induce_eq
-- name    : PerfectGraph.indepNum_induce_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:27:32.839494+00:00
-- url     : https://prove2.me/theorems/55555c0a-a691-5397-910e-85c7e5006a07
-- title:
--   Perfect Graph: indep Num induce eq
-- statement:
--   The Perfect Graph construction uses the indep Num induce eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Gasparian.lean#L87-L89
-- source:
--   https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Gasparian.lean#L87-L89

module
public import Mathlib
public import Definitions.Def_PerfectLib_Gasparian
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open PerfectGraph
variable {V : Type*} (G : SimpleGraph V)

theorem PerfectGraph.indepNum_induce_eq (S : Finset V) :
    (G.induce (S : Set V)).indepNum = (Gᶜ.induce (S : Set V)).cliqueNum := by sorry
