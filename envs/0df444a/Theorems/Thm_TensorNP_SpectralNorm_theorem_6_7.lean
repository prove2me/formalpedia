-- Prove2me | Theorems.Thm_TensorNP_SpectralNorm_theorem_6_7
-- name    : TensorNP.SpectralNorm.theorem_6_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:06:16.05137+00:00
-- url     : https://prove2.me/theorems/0a7390ce-d4f6-4839-bb3f-4ac734c1f9be
-- title:
--   Theorem 6.7 (Motzkin–Straus) — 1 − 1/ω(G) = 2 max over the simplex of Σ_{ij∈E} x_i x_j
-- statement:
--   Let $G=(V,E)$ be a simple graph on $v\ge1$ vertices with clique number $\omega(G)$ (the number of vertices of a largest clique), and let $\Delta_v=\{\mathbf x\in\mathbb R^v_{\ge0}:\sum_{i=1}^v x_i=1\}$ be the standard simplex. Then
--   $$
--   1-\frac1{\omega(G)} = 2\cdot\max_{\mathbf x\in\Delta_v}\sum_{\{i,j\}\in E}x_ix_j ,
--   $$
--   where the sum runs over the unordered edges of $G$, and the maximum is attained.
--
--   This classical theorem of Motzkin and Straus (1965) links the combinatorial quantity $\omega(G)$ to a quadratic optimization problem over the simplex; it is the source of the value of $M_l$ in display (22).
--
--   **Formalization Note** The vertex set is `Fin v` and the clique number is Mathlib's `SimpleGraph.cliqueNum`. The statement is `IsGreatest` of the image of $\Delta_v$ (Mathlib's `stdSimplex ℝ (Fin v)`) under $\mathbf x\mapsto 2\sum_{\{i,j\}\in E}x_ix_j$, which asserts both that the value $1-1/\omega(G)$ is attained and that it is an upper bound. The hypothesis $v\ge1$ (so $\omega(G)\ge1$) excludes the empty graph, for which $1/\omega$ is not defined.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:22, Theorem 6.7 (Motzkin–Straus 1965)

import Mathlib

namespace TensorNP.SpectralNorm

/-- **Theorem 6.7 (Motzkin–Straus).** Let `G` be a simple graph on `v ≥ 1` vertices with clique
number `ω(G)`. Over the standard simplex `Δ_v`, the maximum of `2 Σ_{{i,j} ∈ E} x_i x_j` (sum over
the unordered edges) is `1 − 1/ω(G)`. -/
theorem theorem_6_7 {v : ℕ} (hv : 0 < v) (G : SimpleGraph (Fin v)) [DecidableRel G.Adj] :
    IsGreatest
      ((fun x : Fin v → ℝ =>
          2 * ∑ s ∈ G.edgeFinset, Sym2.lift ⟨fun i j => x i * x j, fun i j => mul_comm _ _⟩ s) ''
        stdSimplex ℝ (Fin v))
      (1 - 1 / (G.cliqueNum : ℝ)) := by sorry

end TensorNP.SpectralNorm
