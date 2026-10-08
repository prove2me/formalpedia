-- Prove2me | Theorems.Thm_SparseNLO_IHT_lemma_2_2
-- name    : SparseNLO.IHT.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:08:07.416105+00:00
-- url     : https://prove2.me/theorems/b47c1836-745f-481d-9c76-b2fdfacc70d2
-- title:
--   Lemma 2.2 — [NC_L] holds iff ‖x‖₀ ≤ s, ∇ᵢf(x) = 0 on the support and |∇ᵢf(x)| ≤ L·M_s(x) off it (2.5)
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be continuously differentiable and bounded below (Assumption 1), and let $0<s<n$. For any $L>0$, a vector $x^*\in\mathbb R^n$ satisfies
--   $$[\mathrm{NC}_L]\qquad x^*\in P_{C_s}\Big(x^*-\tfrac1L\nabla f(x^*)\Big)$$
--   if and only if $\|x^*\|_0\le s$ and
--   $$|\nabla_i f(x^*)|\ \begin{cases}\le L\,M_s(x^*) & \text{if } i\in I_0(x^*),\\ =0 & \text{if } i\in I_1(x^*).\end{cases}\tag{2.5}$$
--
--   Lemma 2.2 turns the projection condition $[\mathrm{NC}_L]$ into explicit coordinate-wise inequalities. It shows that $L$-stationarity becomes weaker as $L$ grows, and it is the form in which the limit argument of Theorem 3.1 verifies $L$-stationarity.
--
--   **Formalization Note** $[\mathrm{NC}_L]$ is the bare membership in the projection set $P_{C_s}$ (the set of all nearest points). Assumption 1 is the paper's standing assumption and is kept although the equivalence does not use it. Indices run over `Fin n`.
-- source:
--   Beck, Eldar, Sparsity Constrained Nonlinear Optimization: Optimality Conditions and Algorithms, SIAM J. Optim. (2013), doi:10.1137/120869778 (source: arXiv:1203.4580v1), p. 7, Lemma 2.2, (2.5)

import Mathlib
import Definitions.Def_SparseNLO_IHT_Setting

open Filter Topology

namespace SparseNLO.IHT

/-- Lemma 2.2 (p. 7). For any `L > 0`, `x` satisfies `[NC_L]`, i.e.
`x ∈ P_{C_s}(x − (1/L) ∇f(x))`, if and only if `‖x‖₀ ≤ s` and (2.5):
`|∇_i f(x)| ≤ L · M_s(x)` for `i ∈ I₀(x)` and `∇_i f(x) = 0` for `i ∈ I₁(x)`. -/
theorem lemma_2_2 {n s : ℕ} (hs : 0 < s) (hsn : s < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f) (hbdd : ∃ γ : ℝ, ∀ x, γ ≤ f x)
    (L : ℝ) (hL : 0 < L) (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ projCs n s (x - (1 / L) • gradient f x) ↔
      (SparseNLO.CWOpt.l0 x ≤ s ∧
        (∀ i ∈ SparseNLO.CWOpt.I0 x, |gradient f x i| ≤ L * SparseNLO.CWOpt.Ms s x) ∧
        (∀ i ∈ SparseNLO.CWOpt.I1 x, gradient f x i = 0)) := by sorry

end SparseNLO.IHT
