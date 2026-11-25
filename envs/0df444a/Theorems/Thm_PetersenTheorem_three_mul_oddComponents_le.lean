-- Prove2me | Theorems.Thm_PetersenTheorem_three_mul_oddComponents_le
-- name    : PetersenTheorem.three_mul_oddComponents_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:12:36.592215+00:00
-- url     : https://prove2.me/theorems/5640d04a-090a-4d78-9f26-087482e3da3e
-- title:
--   Petersen Theorem: three mul odd Components le
-- statement:
--   The Petersen Theorem construction uses the three mul odd Components le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/petersen-matching/blob/77630d6771d3f5a3da2185db2ff451f6c6ed5190/PetersenLib/Petersen.lean#L150-L195
-- source:
--   https://github.com/jtraverso/petersen-matching/blob/77630d6771d3f5a3da2185db2ff451f6c6ed5190/PetersenLib/Petersen.lean#L150-L195

module
public import Mathlib
public import Definitions.Def_PetersenLib_Petersen
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open PetersenTheorem
variable {V : Type*}

theorem PetersenTheorem.three_mul_oddComponents_le [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h3 : G.IsRegularOfDegree 3) (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e)
    {W : Type*} [Finite W] (H : SimpleGraph W) (S : Set W) (e : W ↪ V) (T : Finset V)
    (hdisjT : ∀ w, w ∉ S → e w ∉ T)
    (hclosed : ∀ w, w ∉ S → ∀ y, G.Adj (e w) y → y ∉ T → ∃ w', e w' = y ∧ H.Adj w w' ∧ w' ∉ S) :
    3 * ((⊤ : H.Subgraph).deleteVerts S).coe.oddComponents.ncard ≤
      ∑ y ∈ T, (G.neighborFinset y \ T).card := by sorry
