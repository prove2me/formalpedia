-- Prove2me | Theorems.Thm_WeylPolyhedra_Polyhedron_Supplement_satz7
-- name    : WeylPolyhedra.Polyhedron.Supplement.satz7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:33:45.049803+00:00
-- url     : https://prove2.me/theorems/1c5f4895-294c-4c51-a2b8-3ebc0789408f
-- title:
--   Satz 7 — $\pi \in (S)$ iff $(x\pi) \ge 0$ for all $x \in (\Sigma)$
-- statement:
--   Let $S \subseteq \mathbb{R}^n$ be a finite non-degenerate system of homogeneous inequalities $(a\xi) \ge 0$, $a \in S$, with region $(S)$. Let $\Sigma$ be its dual system: its inequalities are $(\alpha x) \ge 0$ for the extreme solutions $\alpha$ of $S$, and $(\Sigma)$ is its region. For every $\pi \in \mathbb{R}^n$,
--   $$\pi \in (S) \iff (x\pi) \ge 0 \text{ for all } x \in (\Sigma).$$
--
--   This is the "dual" of Satz 6, which characterizes $(\Sigma)$ by $(S)$. Together they describe each of the two cones $(S)$ and $(\Sigma)$ as the set of vectors nonnegative on the other.
--
--   (Weyl: "Satz 7. π gehört zu (S) dann und nur dann, wenn (xπ) ≧ 0 für alle x in (Σ).")
--
--   **Formalization Note** Non-degeneracy is the hypothesis of Satz 4, from which Satz 5–7 are derived on p. 297. It is needed: for $S = \{e_1\} \subseteq \mathbb{R}^2$ the extreme solutions are the positive multiples of $e_2$ and of $-e_2$, so $(\Sigma) = \{x : x_2 = 0\}$. Then $\pi = e_1$ lies in $(S)$, but $x = (-1, 0) \in (\Sigma)$ gives $(x\pi) = -1 < 0$.
--
--   Differences from the source:
--   - encoding: S non-degenerate, stated once in Satz 4 ("Ist S nicht-ausgeartet") and inherited by Satz 5-8 → explicit hypothesis Shared.NonDegenerate S; reason: standing assumption of the section made explicit; it changes no instance of the source's claim
-- source:
--   Weyl, Elementare Theorie der konvexen Polyeder, Comment. Math. Helv. (1935), p. 297, Satz 7

import Mathlib
import Definitions.Def_WeylPolyhedra_Shared_NonDegenerate
import Definitions.Def_WeylPolyhedra_Polyhedron_Duality

namespace WeylPolyhedra.Polyhedron.Supplement

/-- Weyl (1935), §3 I, p. 297, Satz 7 (the "dual" of Satz 6): let `S ⊆ ℝⁿ` be a finite
non-degenerate system of inequalities `a ⬝ᵥ ξ ≥ 0` (non-degeneracy is the hypothesis of Satz 4,
from which Satz 5–7 are derived). Then `π` lies in `(S)` if and only if `x ⬝ᵥ π ≥ 0` for every
`x` in the region `(Σ)` of the dual system. -/
theorem satz7 {n : ℕ} (S : Finset (Fin n → ℝ)) (hS : Shared.NonDegenerate S) (π : Fin n → ℝ) :
    π ∈ solutionRegion S ↔ ∀ x ∈ dualRegion S, 0 ≤ x ⬝ᵥ π := by sorry

end WeylPolyhedra.Polyhedron.Supplement
