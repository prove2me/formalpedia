-- Prove2me | Theorems.Thm_SparseNLO_Partial_lemma_2_2
-- name    : SparseNLO.Partial.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T15:12:34.278933+00:00
-- url     : https://prove2.me/theorems/4a189a54-520f-4879-a2d9-8bc459524707
-- title:
--   Lemma 2.2 — [NC_L] iff ‖x‖₀ ≤ s and the coordinate conditions (2.5)
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be continuously differentiable and bounded below, let $0<s<n$, and let $L>0$. For every $x\in\mathbb R^n$, the condition $[\mathrm{NC}_L]$, $x\in P_{C_s}\big(x-\tfrac1L\nabla f(x)\big)$, holds if and only if $\|x\|_0\le s$ and
--   $$|\nabla_if(x)|\ \begin{cases}\le L\,M_s(x), & i\in I_0(x),\\ =0, & i\in I_1(x).\end{cases} \tag{2.5}$$
--
--   The lemma replaces the projection condition by explicit coordinate conditions. In this mission it turns the coordinate bounds reached at a limit point of the partial sparse-simplex method into $L_2(f)$-stationarity.
--
--   **Formalization Note** $P_{C_s}(y)$ is the set of nearest points of $C_s$ to $y$. Assumption 1 is kept as the paper's standing hypothesis, though the statement does not need it.
-- source:
--   Beck, Eldar, Sparsity Constrained Nonlinear Optimization: Optimality Conditions and Algorithms, SIAM J. Optim. (2013), doi:10.1137/120869778 (source: arXiv:1203.4580v1), p. 7, Lemma 2.2 (2.5)

import Mathlib
import Definitions.Def_SparseNLO_Partial_Setting

namespace SparseNLO.Partial

/-- Lemma 2.2 (p. 7). For any `L > 0`, `x` satisfies `[NC_L]`, i.e.
`x ∈ P_{C_s}(x − (1/L) ∇f(x))`, if and only if `‖x‖₀ ≤ s` and (2.5):
`|∇_i f(x)| ≤ L · M_s(x)` for `i ∈ I₀(x)` and `∇_i f(x) = 0` for `i ∈ I₁(x)`. -/
theorem lemma_2_2 {n s : ℕ} (hs : 0 < s) (hsn : s < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f) (hbdd : ∃ γ : ℝ, ∀ x, γ ≤ f x)
    (L : ℝ) (hL : 0 < L) (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ projCs n s (x - (1 / L) • gradient f x) ↔
      (l0 x ≤ s ∧
        (∀ i ∈ I0 x, |gradient f x i| ≤ L * Ms s x) ∧
        (∀ i ∈ I1 x, gradient f x i = 0)) := by sorry

end SparseNLO.Partial
