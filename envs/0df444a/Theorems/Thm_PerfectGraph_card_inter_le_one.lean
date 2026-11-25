-- Prove2me | Theorems.Thm_PerfectGraph_card_inter_le_one
-- name    : PerfectGraph.card_inter_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:28:15.671866+00:00
-- url     : https://prove2.me/theorems/fbbfe06b-8528-4fd2-a47a-069d7c898046
-- title:
--   Perfect Graph: card inter le one
-- statement:
--   The Perfect Graph construction uses the card inter le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Gasparian.lean#L108-L115
-- source:
--   https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Gasparian.lean#L108-L115

module
public import Mathlib
public import Definitions.Def_PerfectLib_Gasparian
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open PerfectGraph
variable {V : Type*} (G : SimpleGraph V)

theorem PerfectGraph.card_inter_le_one [DecidableEq V] {K A : Finset V} (hK : G.IsClique (K : Set V))
    (hA : G.IsIndepSet (A : Set V)) : (K ∩ A).card ≤ 1 := by sorry
