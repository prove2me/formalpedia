-- Prove2me | Theorems.Thm_WeylPolyhedra_Polyhedron_satz6
-- name    : WeylPolyhedra.Polyhedron.satz6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:04:37.424637+00:00
-- url     : https://prove2.me/theorems/41eca010-8baf-4251-bd2c-a097f0400975
-- title:
--   Satz 6: $p \in (\Sigma)$ iff $(p\xi) \ge 0$ for all $\xi \in (S)$
-- statement:
--   Let $S \subseteq \mathbb{R}^n$ be a finite non-degenerate system of homogeneous inequalities $(a\xi) \ge 0$, $a \in S$, with solution region $(S)$, and let $\Sigma$ be its dual system, whose inequalities are $(\alpha x) \ge 0$ for the extreme solutions $\alpha$ of $S$. For every $p \in \mathbb{R}^n$,
--   $$p \in (\Sigma) \iff (p\xi) \ge 0 \text{ for all } \xi \in (S).$$
--
--   In words: the finitely many extreme solutions of $S$ already cut out the whole dual cone of $(S)$. Together with Satz 7 it sets up the duality between $S$ and $\Sigma$ that §4 transfers to convex polyhedra.
--
--   (Weyl: "Satz 6. p gehört zu (Σ) dann und nur dann, wenn (pξ) ≧ 0 ist für alle ξ in (S).")
--
--   **Formalization Note** Satz 6 is Weyl's sharpening of Satz 4 ("Darum können wir Satz 4 so aussprechen … Und genauer"), whose hypothesis "Ist S nicht-ausgeartet" is carried over explicitly. Without it the statement is false: for $S = \{e_1\} \subseteq \mathbb{R}^2$, $p = (-1, 0)$ lies in $(\Sigma)$ but $(p e_1) < 0$ with $e_1 \in (S)$.
-- source:
--   Weyl, Elementare Theorie der konvexen Polyeder, Comment. Math. Helv. (1935), p. 297, Satz 6

import Mathlib
import Definitions.Def_WeylPolyhedra_Shared_NonDegenerate
import Definitions.Def_WeylPolyhedra_Polyhedron_Duality

namespace WeylPolyhedra.Polyhedron

/-- Weyl (1935), §3, p. 297, Satz 6: let `S ⊆ ℝⁿ` be a finite non-degenerate system of
inequalities `a ⬝ᵥ ξ ≥ 0` (non-degeneracy is the standing hypothesis of Satz 4, which Satz 6
restates). Then `p` lies in the region `(Σ)` of the dual system — `α ⬝ᵥ p ≥ 0` for every
extreme solution `α` of `S` — if and only if `p ⬝ᵥ ξ ≥ 0` for every `ξ ∈ (S)`. -/
theorem satz6 {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S) (p : Fin n → ℝ) :
    p ∈ dualRegion S ↔ ∀ ξ ∈ solutionRegion S, 0 ≤ p ⬝ᵥ ξ := by sorry

end WeylPolyhedra.Polyhedron
