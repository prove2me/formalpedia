-- Prove2me | Theorems.Thm_SolodovSvaiterVI_Alg21_lemma2_1_projection_properties
-- name    : SolodovSvaiterVI.Alg21.lemma2_1_projection_properties
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T10:18:31.317858+00:00
-- url     : https://prove2.me/theorems/8a2ec3e8-910c-4a6e-8381-657b97da8ad6
-- title:
--   Lemma 2.1 — obtuse-angle property and firm nonexpansiveness of the projection
-- statement:
--   Let $B$ be a nonempty closed convex subset of $\mathbb{R}^n$ and let $P_B$ denote the Euclidean projection onto $B$. Then for all $x, y \in \mathbb{R}^n$ and every $z \in B$:
--
--   1. $$\langle x - P_B[x],\ z - P_B[x] \rangle \le 0;$$
--   2. $$\|P_B[x] - P_B[y]\|^2 \le \|x - y\|^2 - \|P_B[x] - x + y - P_B[y]\|^2.$$
--
--   Property 1 characterizes the projection as the point of $B$ at which $x$ sees every other point of $B$ at an obtuse angle; property 2 is the firm nonexpansiveness of $P_B$. Both are used repeatedly in the convergence analysis of Algorithm 2.1.
--
--   **Formalization Note** $P_B$ is `projOnto B`; under the hypotheses it is the true projection.
-- source:
--   Solodov & Svaiter, A New Projection Method for Variational Inequality Problems, SIAM J. Control Optim. 37 (1999), p. 768, Lemma 2.1

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_projOnto

open scoped InnerProductSpace

namespace SolodovSvaiterVI.Alg21

/-- Lemma 2.1 of Solodov–Svaiter (p. 768): for a nonempty closed convex `B ⊆ ℝⁿ`, any
`x, y ∈ ℝⁿ` and any `z ∈ B`,
1. `⟨x − P_B[x], z − P_B[x]⟩ ≤ 0`;
2. `‖P_B[x] − P_B[y]‖² ≤ ‖x − y‖² − ‖P_B[x] − x + y − P_B[y]‖²`. -/
theorem lemma2_1_projection_properties {n : ℕ} (B : Set (EuclideanSpace ℝ (Fin n)))
    (hBne : B.Nonempty) (hBc : IsClosed B) (hBcv : Convex ℝ B)
    (x y z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ B) :
    ⟪x - projOnto B x, z - projOnto B x⟫_ℝ ≤ 0 ∧
      ‖projOnto B x - projOnto B y‖ ^ 2 ≤
        ‖x - y‖ ^ 2 - ‖projOnto B x - x + y - projOnto B y‖ ^ 2 := by sorry

end SolodovSvaiterVI.Alg21
