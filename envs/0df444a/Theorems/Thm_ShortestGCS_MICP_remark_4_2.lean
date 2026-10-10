-- Prove2me | Theorems.Thm_ShortestGCS_MICP_remark_4_2
-- name    : ShortestGCS.MICP.remark_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:10:19.422441+00:00
-- url     : https://prove2.me/theorems/bd1ea5bf-c747-4a42-afb0-99301548f571
-- title:
--   Remark 4.2, p. 5 — for bounded closed 𝒳 the closure in the perspective 𝒳̃ is unnecessary
-- statement:
--   Let $\mathcal X \subseteq \mathbb R^n$ be closed and bounded. Then the closure in Definition 4.1 can be dropped:
--
--   $$
--   \tilde{\mathcal X} = \{(x,\lambda) : \lambda \ge 0,\ x \in \lambda\mathcal X\}.
--   $$
--
--   In particular the slice of $\tilde{\mathcal X}$ at $\lambda = 0$ is $\{0\}$ when $\mathcal X$ is nonempty, and the slice at $\lambda = 1$ is $\mathcal X$ itself. This is what makes the constraint (5.5e) of the MICP force $z_e = z'_e = 0$ on edges with zero flow and $z_e \in \mathcal X_u$, $z'_e \in \mathcal X_v$ on edges with unit flow.
--
--   **Formalization Note** Convexity of $\mathcal X$, which is part of the scope of Definition 4.1, is not assumed; the statement without it is stronger. Closedness is kept: for a bounded set that is not closed, such as $(0,1]$, the closure does matter.
-- source:
--   Marcucci, Umenberger, Parrilo & Tedrake, Shortest Paths in Graphs of Convex Sets, arXiv:2101.11565v5, Remark 4.2, p. 5 (first sentence)

import Mathlib
import Definitions.Def_ShortestGCS_MICP_Perspective

open Pointwise

namespace ShortestGCS.MICP

/-- Remark 4.2, arXiv:2101.11565v5, p. 5: for a bounded closed set `𝒳 ⊆ ℝⁿ` the closure in
Definition 4.1 is unnecessary. (Convexity, part of Definition 4.1's scope, is not needed.) -/
theorem remark_4_2 {n : ℕ} (X : Set (Fin n → ℝ)) (hclosed : IsClosed X)
    (hbdd : Bornology.IsBounded X) :
    perspectiveSet X = {q : (Fin n → ℝ) × ℝ | 0 ≤ q.2 ∧ q.1 ∈ q.2 • X} := by sorry

end ShortestGCS.MICP
