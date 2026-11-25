-- Prove2me | Theorems.Thm_PetersenTheorem_three_mul_card_le
-- name    : PetersenTheorem.three_mul_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:12:31.858409+00:00
-- url     : https://prove2.me/theorems/2029e69e-9ccc-5f24-a5c0-eb22a147fec0
-- title:
--   Petersen Theorem: three mul card le
-- statement:
--   The Petersen Theorem construction uses the three mul card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/petersen-matching/blob/77630d6771d3f5a3da2185db2ff451f6c6ed5190/PetersenLib/Petersen.lean#L108-L146
-- source:
--   https://github.com/jtraverso/petersen-matching/blob/77630d6771d3f5a3da2185db2ff451f6c6ed5190/PetersenLib/Petersen.lean#L108-L146

module
public import Mathlib
public import Definitions.Def_PetersenLib_Petersen
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open PetersenTheorem
variable {V : Type*}
variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem PetersenTheorem.three_mul_card_le {ι : Type*} (h3 : G.IsRegularOfDegree 3)
    (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) (O : Finset ι) (f : ι → Finset V) (T : Finset V)
    (hdisj : (O : Set ι).PairwiseDisjoint f) (hT : ∀ i ∈ O, Disjoint (f i) T)
    (hclosed : ∀ i ∈ O, ∀ x ∈ f i, ∀ y, G.Adj x y → y ∉ T → y ∈ f i)
    (hodd : ∀ i ∈ O, Odd (f i).card) :
    3 * O.card ≤ ∑ y ∈ T, (G.neighborFinset y \ T).card := by sorry
