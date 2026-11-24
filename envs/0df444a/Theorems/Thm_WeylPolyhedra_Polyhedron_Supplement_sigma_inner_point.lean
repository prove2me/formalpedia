-- Prove2me | Theorems.Thm_WeylPolyhedra_Polyhedron_Supplement_sigma_inner_point
-- name    : WeylPolyhedra.Polyhedron.Supplement.sigma_inner_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:36:13.412249+00:00
-- url     : https://prove2.me/theorems/d1a5cfac-87f5-4224-b48a-004aa97dd5b0
-- title:
--   §3 III, p. 299 (remark) — the centre $a + b + \cdots$ of $S$ is an inner point of $(\Sigma)$
-- statement:
--   Let $S \subseteq \mathbb{R}^n$ be a finite non-degenerate system of homogeneous inequalities $(a\xi) \ge 0$, $a \in S$, whose region $(S)$ contains an inner point $\xi^0$ ($(a\xi^0) > 0$ for every $a \in S$): the hypotheses of Satz 9. Then the region $(\Sigma)$ of the dual system also has inner points; the centre of $S$, the sum of its points, is one:
--   $$(\alpha\,c) > 0 \quad \text{for every extreme solution } \alpha \text{ of } S, \qquad c = \sum_{s \in S} s.$$
--
--   Applied to $\Sigma$ in place of $S$, it gives the inner point that Satz 9 needs to make $S'$ non-degenerate, which is used in Satz 11.
--
--   (Weyl: "Wir fügen hinzu, daß unter den Voraussetzungen von Satz 9, die für den Rest dieses Paragraphen beibehalten werden, auch (Σ) innere Punkte enthält: das Zentrum a + b + ⋯ von S ist z. B. ein solcher innerer Punkt.")
--
--   **Formalization Note** An inner point of the region of a system is one at which every inequality is strict, as Weyl defines it on p. 299. The centre is the sum over the finite set $S$.
--
--   Differences from the source:
--   - encoding: the hypotheses of Satz 9, "die für den Rest dieses Paragraphen beibehalten werden" (p. 299) → explicit hypotheses Shared.NonDegenerate S and ∃ ξ₀, ∀ a ∈ S, 0 < a ⬝ᵥ ξ₀; reason: standing assumptions of the rest of §3 made explicit; they change no instance of the source's claim
-- source:
--   Weyl, Elementare Theorie der konvexen Polyeder, Comment. Math. Helv. (1935), pp. 299–300, §3 III (remark after Satz 9)

import Mathlib
import Definitions.Def_WeylPolyhedra_Shared_NonDegenerate
import Definitions.Def_WeylPolyhedra_Polyhedron_Duality

namespace WeylPolyhedra.Polyhedron.Supplement

/-- Weyl (1935), §3 III, pp. 299–300 (remark after Satz 9): under the hypotheses of Satz 9 —
`S ⊆ ℝⁿ` finite and non-degenerate, and `(S)` containing an inner point `ξ⁰`
(`a ⬝ᵥ ξ⁰ > 0` for every `a ∈ S`) — the region `(Σ)` of the dual system also has inner points:
the centre `a + b + ⋯` of `S` satisfies every inequality of `Σ` strictly. -/
theorem sigma_inner_point {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S)
    (hint : ∃ ξ₀ : Fin n → ℝ, ∀ a ∈ S, 0 < a ⬝ᵥ ξ₀) :
    ∀ α : Fin n → ℝ, IsExtremeSolution S α → 0 < α ⬝ᵥ ∑ s ∈ S, s := by sorry

end WeylPolyhedra.Polyhedron.Supplement
