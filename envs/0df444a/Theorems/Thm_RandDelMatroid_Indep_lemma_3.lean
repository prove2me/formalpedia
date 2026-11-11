-- Prove2me | Theorems.Thm_RandDelMatroid_Indep_lemma_3
-- name    : RandDelMatroid.Indep.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:29:08.239506+00:00
-- url     : https://prove2.me/theorems/75f3b244-eea5-4dee-a02b-f0af5c4e743b
-- title:
--   Lemma 3 [Sey80] — circuits of a 1-, 2- or 3-sum
-- statement:
--   Let $M_1=(E_1,\mathcal I_1)$ and $M_2=(E_2,\mathcal I_2)$ be binary matroids, $S=E_1\cap E_2$, and let $\mathcal C_1,\mathcal C_2$ be their families of circuits. Let $M=M_1\triangle M_2$ be a 1-sum, 2-sum or 3-sum. Then for every circuit $C$ of $M$ exactly one of the following holds:
--
--   1. $C\in\mathcal C_1$ and $S\cap C=\emptyset$;
--   2. $C\in\mathcal C_2$ and $S\cap C=\emptyset$;
--   3. there exist unique $e\in S$, $C_1\in\mathcal C_1$ and $C_2\in\mathcal C_2$ such that
--
--   $$S\cap C_1=S\cap C_2=\{e\}\quad\text{and}\quad C=C_1\triangle C_2.$$
--
--   The lemma is how a circuit of an assembled matroid is split across a tree edge in the proof of Lemma 7.
--
--   **Formalization Note** "Exactly one" is the disjunction of the three cases each with the other two negated; uniqueness in case 3 is `∃!` over the triple $(e,C_1,C_2)$.
--
--   Differences from the source:
--   - encoding: matroid M = (E, I) with E a finite ground set (Definition 1) → Mathlib Matroid on an element type with finite ground set M.E; reason: Definition 1's matroids are finite; any finite matroid is a Lean Matroid with finite ground set
-- source:
--   Karthekeyan Chandrasekaran, Chandra Chekuri, Weihao Zhu, STOC 2027 submission #536 (October 2026), p. 11, Lemma 3

import Mathlib
import Definitions.Def_RandDelMatroid_Indep_Regular
import Definitions.Def_RandDelMatroid_Indep_Sums

set_option autoImplicit false

open scoped NNReal

namespace RandDelMatroid.Indep

/-- Lemma 3 ([Sey80], p. 11). Let `M₁, M₂` be binary matroids, `S = E₁ ∩ E₂`, and `N = M₁ △ M₂` a
1-, 2- or 3-sum. For every circuit `C` of `N`, exactly one of the following holds:
1. `C` is a circuit of `M₁` with `S ∩ C = ∅`;
2. `C` is a circuit of `M₂` with `S ∩ C = ∅`;
3. there exist unique `e ∈ S`, a circuit `C₁` of `M₁` and a circuit `C₂` of `M₂` with
   `S ∩ C₁ = S ∩ C₂ = {e}` and `C = C₁ △ C₂`. -/
theorem lemma_3 {β : Type} (M₁ M₂ N : Matroid β) [M₁.Finite] [M₂.Finite]
    (h₁ : IsBinary M₁) (h₂ : IsBinary M₂)
    (hN : IsOneSum M₁ M₂ N ∨ IsTwoSum M₁ M₂ N ∨ IsThreeSum M₁ M₂ N)
    (C : Set β) (hC : N.IsCircuit C) :
    let S := M₁.E ∩ M₂.E
    let P₁ : Prop := M₁.IsCircuit C ∧ S ∩ C = ∅
    let P₂ : Prop := M₂.IsCircuit C ∧ S ∩ C = ∅
    let P₃ : Prop := ∃! t : β × Set β × Set β, t.1 ∈ S ∧ M₁.IsCircuit t.2.1 ∧
      M₂.IsCircuit t.2.2 ∧ S ∩ t.2.1 = {t.1} ∧ S ∩ t.2.2 = {t.1} ∧ C = symmDiff t.2.1 t.2.2
    (P₁ ∧ ¬ P₂ ∧ ¬ P₃) ∨ (¬ P₁ ∧ P₂ ∧ ¬ P₃) ∨ (¬ P₁ ∧ ¬ P₂ ∧ P₃) := by sorry

end RandDelMatroid.Indep
