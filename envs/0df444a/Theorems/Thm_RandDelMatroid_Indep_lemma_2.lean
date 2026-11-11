-- Prove2me | Theorems.Thm_RandDelMatroid_Indep_lemma_2
-- name    : RandDelMatroid.Indep.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:29:08.184437+00:00
-- url     : https://prove2.me/theorems/8527a9f8-e322-4730-b4a8-0b64c29cd37f
-- title:
--   Lemma 2 — symmetric differences in a sum are disjoint unions of circuits
-- statement:
--   Let $M_1=(E_1,\mathcal I_1)$ and $M_2=(E_2,\mathcal I_2)$ be binary matroids, $S=E_1\cap E_2$, and $M=M_1\triangle M_2$ their sum (Definition 9). Let $C_i$ be a (possibly empty) disjoint union of circuits of $M_i$, $i=1,2$. If $C_1\cap S=C_2\cap S$, then
--
--   $$C_1\triangle C_2 \text{ is a disjoint union of circuits of } M.$$
--
--   This is the circuit calculus behind the cycle description of sums used throughout the paper (Lemmas 7, 14, 15, 16).
--
--   Differences from the source:
--   - encoding: matroid M = (E, I) with E a finite ground set (Definition 1) → Mathlib Matroid on an element type with finite ground set M.E; reason: Definition 1's matroids are finite; any finite matroid is a Lean Matroid with finite ground set
-- source:
--   Karthekeyan Chandrasekaran, Chandra Chekuri, Weihao Zhu, STOC 2027 submission #536 (October 2026), p. 10, Lemma 2

import Mathlib
import Definitions.Def_RandDelMatroid_Indep_Regular
import Definitions.Def_RandDelMatroid_Indep_Sums

set_option autoImplicit false

open scoped NNReal

namespace RandDelMatroid.Indep

/-- Lemma 2 (p. 10). Let `M₁, M₂` be binary matroids, `S = E₁ ∩ E₂`, and `N = M₁ △ M₂` their sum.
If `Cᵢ` is a (possibly empty) disjoint union of circuits of `Mᵢ` and `C₁ ∩ S = C₂ ∩ S`, then
`C₁ △ C₂` is a disjoint union of circuits of `N`. -/
theorem lemma_2 {β : Type} (M₁ M₂ N : Matroid β) [M₁.Finite] [M₂.Finite]
    (h₁ : IsBinary M₁) (h₂ : IsBinary M₂) (hN : IsSum M₁ M₂ N) (C₁ C₂ : Set β)
    (hC₁ : IsCycle M₁ C₁) (hC₂ : IsCycle M₂ C₂)
    (hS : C₁ ∩ (M₁.E ∩ M₂.E) = C₂ ∩ (M₁.E ∩ M₂.E)) :
    IsCycle N (symmDiff C₁ C₂) := by sorry

end RandDelMatroid.Indep
