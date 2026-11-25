-- Prove2me | Theorems.Thm_PerfectGraph_colorable_induce_iff
-- name    : PerfectGraph.colorable_induce_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T10:27:59.313481+00:00
-- url     : https://prove2.me/theorems/44adab9b-d283-43f4-b574-0e5a4a0b789b
-- title:
--   Perfect Graph: colorable induce iff
-- statement:
--   The Perfect Graph construction uses the colorable induce iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Gasparian.lean#L29-L45
-- source:
--   https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Gasparian.lean#L29-L45

module
public import Mathlib
public import Definitions.Def_PerfectLib_Gasparian
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open PerfectGraph
variable {V : Type*} (G : SimpleGraph V)

theorem PerfectGraph.colorable_induce_iff (S : Finset V) (k : ℕ) :
    (G.induce (S : Set V)).Colorable k ↔ IsColOn G S k := by sorry
