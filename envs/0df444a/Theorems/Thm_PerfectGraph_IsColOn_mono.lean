-- Prove2me | Theorems.Thm_PerfectGraph_IsColOn_mono
-- name    : PerfectGraph.IsColOn.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:33:44.168202+00:00
-- url     : https://prove2.me/theorems/c4c3346b-8aeb-46ac-aaea-854075018b63
-- title:
--   Is Col On: mono
-- statement:
--   The Is Col On construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Gasparian.lean#L47-L50
-- source:
--   https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Gasparian.lean#L47-L50

module
public import Mathlib
public import Definitions.Def_PerfectLib_Gasparian
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open PerfectGraph
variable {V : Type*} (G : SimpleGraph V)

theorem PerfectGraph.IsColOn.mono {S : Finset V} {k l : ℕ} (h : IsColOn G S k) (hkl : k ≤ l) :
    IsColOn G S l := by sorry
