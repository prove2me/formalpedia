-- Prove2me | Theorems.Thm_PerfectGraph_card_le_of_isColOn
-- name    : PerfectGraph.card_le_of_isColOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:31:14.432462+00:00
-- url     : https://prove2.me/theorems/33944782-8737-4f58-b533-0b5aa2db294e
-- title:
--   Perfect Graph: card le of is Col On
-- statement:
--   The Perfect Graph construction uses the card le of is Col On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Gasparian.lean#L310-L325
-- source:
--   https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Gasparian.lean#L310-L325

module
public import Mathlib
public import Definitions.Def_PerfectLib_Gasparian
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open PerfectGraph
variable {V : Type*} (G : SimpleGraph V)

theorem PerfectGraph.card_le_of_isColOn [Finite V] {S : Finset V} {k : ℕ} (h : IsColOn G S k) :
    S.card ≤ (G.induce (S : Set V)).indepNum * k := by sorry
