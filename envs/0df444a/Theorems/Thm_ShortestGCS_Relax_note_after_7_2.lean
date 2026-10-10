-- Prove2me | Theorems.Thm_ShortestGCS_Relax_note_after_7_2
-- name    : ShortestGCS.Relax.note_after_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:59:50.275815+00:00
-- url     : https://prove2.me/theorems/0abca4aa-0e4d-4a34-a6a8-1fb7e8261c9e
-- title:
--   §7.1, p. 12 (after (7.2)) — the inequalities of 𝒮′ imply x ∈ 𝒳 and y ∈ 𝒴
-- statement:
--   Let $\mathcal X \subseteq \mathbb R^n$ and $\mathcal Y \subseteq \mathbb R^m$ be closed convex sets and let $\mathcal S'$ be the relaxation (7.2). Then every $(x, y, Z) \in \mathcal S'$ satisfies
--
--   $$
--   x \in \mathcal X \quad\text{and}\quad y \in \mathcal Y .
--   $$
--
--   In the paper this is obtained from the inequalities of (7.2) corresponding to $(0, 1) \in \mathcal Y^\circ$ and $(0, 1) \in \mathcal X^\circ$. It is the first step of the proof of Lemma 7.4.
--
--   **Formalization Note** No nonemptiness is assumed: if $\mathcal X = \emptyset$ then $(0, -1) \in \mathcal X^\circ$ and $\mathcal S' = \emptyset$.
-- source:
--   arXiv:2101.11565v5, §7.1, p. 12, the sentence after (7.2)

import Mathlib
import Definitions.Def_ShortestGCS_MICP_Perspective
import Definitions.Def_ShortestGCS_Relax_Setting

namespace ShortestGCS.Relax

/-- §7.1, p. 12, the sentence after (7.2), arXiv:2101.11565v5: for closed convex `𝒳` and `𝒴`, the
inequalities of `𝒮′` imply `x ∈ 𝒳` and `y ∈ 𝒴`. -/
theorem note_after_7_2 {n m : ℕ} (X : Set (Fin n → ℝ)) (Y : Set (Fin m → ℝ))
    (hXc : IsClosed X) (hXcv : Convex ℝ X) (hYc : IsClosed Y) (hYcv : Convex ℝ Y) :
    relaxSet X Y ⊆ {w | w.1 ∈ X ∧ w.2.1 ∈ Y} := by sorry

end ShortestGCS.Relax
