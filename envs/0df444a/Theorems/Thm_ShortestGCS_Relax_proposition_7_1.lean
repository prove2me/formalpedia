-- Prove2me | Theorems.Thm_ShortestGCS_Relax_proposition_7_1
-- name    : ShortestGCS.Relax.proposition_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:59:08.775789+00:00
-- url     : https://prove2.me/theorems/b2236801-b343-4432-a68e-af0deb0414a4
-- title:
--   Proposition 7.1, p. 12 — 𝒮′ equals the asymmetric relaxation (7.3), when 1 ≥ 0 is a nonnegative combination of the rows
-- statement:
--   Let $\mathcal X \subseteq \mathbb R^n$ be a closed convex set and let $\mathcal Y = \{y : c_i^\top y + d_i \ge 0 \text{ for all } i \in \mathcal I\}$ be a polytope with finite index set $\mathcal I$. Assume that there are $\alpha_i \ge 0$ with
--
--   $$
--   \sum_{i \in \mathcal I} \alpha_i c_i = 0, \qquad \sum_{i \in \mathcal I} \alpha_i d_i = 1 .
--   $$
--
--   Then
--
--   $$
--   \mathcal S' = \{(x, y, Z) : (Zc_i + d_i x,\ c_i^\top y + d_i) \in \tilde{\mathcal X} \text{ for all } i \in \mathcal I\}. \qquad (7.3)
--   $$
--
--   The right side involves only $|\mathcal I|$ perspective-cone constraints, so it is a finite, computationally usable description of the relaxation $\mathcal S'$.
--
--   **Formalization Note** The hypothesis on the $\alpha_i$ (the trivial inequality $1 \ge 0$ is a nonnegative combination of the defining inequalities) is added. Without it the proposition is false: with $\mathcal Y = \{0\} \subset \mathbb R$ written as $\{y \ge 0, -y \ge 0\}$ and $\mathcal X = [0, 1]$, the point $(x, y, Z) = (5, 0, 0)$ satisfies (7.3) but violates the inequality of $\mathcal S'$ for $(a, b) = (-1, 1) \in \mathcal X^\circ$ and $(c, d) = (0, 1) \in \mathcal Y^\circ$ (its value is $-5 + 1 = -4$); the paper's step "any vector $(c, d) \in \mathcal Y^\circ$ can be expressed as $\sum_i \alpha_i (c_i, d_i)$" fails for $(c, d) = (0, 1)$. The hypothesis holds whenever the polytope $\mathcal Y$ has an interior point, and for the polytopes $\mathcal Y_v$ of the shortest-path formulation. Nonemptiness of $\mathcal X$ is not assumed.
-- source:
--   arXiv:2101.11565v5, Proposition 7.1, (7.3), p. 12

import Mathlib
import Definitions.Def_ShortestGCS_MICP_Perspective
import Definitions.Def_ShortestGCS_Relax_Setting

namespace ShortestGCS.Relax

/-- Proposition 7.1, arXiv:2101.11565v5, p. 12, with the disclosed hypothesis `hcone` (the trivial inequality
`1 ≥ 0` is a nonnegative combination of the defining inequalities): for a closed convex `𝒳` and a polytope
`𝒴 = {y : cᵢᵀy + dᵢ ≥ 0 ∀ i ∈ ℐ}`, `𝒮′` equals the set (7.3). -/
theorem proposition_7_1 {n m : ℕ} {ι : Type*} [Fintype ι] (X : Set (Fin n → ℝ)) (hXc : IsClosed X)
    (hXcv : Convex ℝ X) (c : ι → Fin m → ℝ) (d : ι → ℝ)
    (hY : Bornology.IsBounded (polyhedron c d))
    (hcone : ∃ α : ι → ℝ, (∀ i, 0 ≤ α i) ∧ ∑ i, α i • c i = 0 ∧ ∑ i, α i * d i = 1) :
    relaxSet X (polyhedron c d) = asymRelaxSet X c d := by sorry

end ShortestGCS.Relax
