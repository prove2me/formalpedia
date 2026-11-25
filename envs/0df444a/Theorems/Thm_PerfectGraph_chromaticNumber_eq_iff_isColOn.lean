-- Prove2me | Theorems.Thm_PerfectGraph_chromaticNumber_eq_iff_isColOn
-- name    : PerfectGraph.chromaticNumber_eq_iff_isColOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:30:57.937379+00:00
-- url     : https://prove2.me/theorems/e3521b36-37c3-4602-aabc-5ad66e36cec3
-- title:
--   Perfect Graph: chromatic Number eq iff is Col On
-- statement:
--   The Perfect Graph construction uses the chromatic Number eq iff is Col On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Gasparian.lean#L304-L308
-- source:
--   https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Gasparian.lean#L304-L308

module
public import Mathlib
public import Definitions.Def_PerfectLib_Gasparian
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open PerfectGraph
variable {V : Type*} (G : SimpleGraph V)

theorem PerfectGraph.chromaticNumber_eq_iff_isColOn (S : Finset V) :
    (G.induce (S : Set V)).chromaticNumber = (G.induce (S : Set V)).cliqueNum ↔
      IsColOn G S (G.induce (S : Set V)).cliqueNum := by sorry
