-- Prove2me | Theorems.Thm_SparseNLO_CWOpt_theorem_2_4
-- name    : SparseNLO.CWOpt.theorem_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T15:12:24.120628+00:00
-- url     : https://prove2.me/theorems/2ca40336-f0b0-432a-99fe-f0ac24d7323c
-- title:
--   Theorem 2.4 — every CW-minimum x* of (P) satisfies |∇ᵢf(x*)| ≤ L₂(f)M_s(x*) on I₀(x*) and ∇ᵢf(x*) = 0 on I₁(x*)
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be continuously differentiable and bounded below (Assumption 1), with $L(f)$-Lipschitz gradient (Assumption 2), and let $0<s<n$ be an integer. Let $L_2$ be a constant satisfying the local Lipschitz condition (2.15), for instance the local Lipschitz constant $L_2(f)$. If $x^*$ is a coordinate-wise minimum of
--   $$\min\ f(x)\quad\text{s.t.}\quad\|x\|_0\le s,$$
--   then
--   $$|\nabla_i f(x^*)|\ \begin{cases}\le L_2\,M_s(x^*), & i\in I_0(x^*),\\ =0, & i\in I_1(x^*),\end{cases}\qquad(2.16)$$
--   where $M_s(x^*)$ is the $s$-th largest absolute value of the components of $x^*$. That is, $x^*$ is an $L_2(f)$-stationary point.
--
--   The theorem places coordinate-wise minimality above $L$-stationarity in the hierarchy of necessary optimality conditions for sparsity constrained problems, with the local constant $L_2(f)\le L(f)$ in place of the global Lipschitz constant. Since every optimal solution of (P) is a CW-minimum, every optimal solution is an $L_2(f)$-stationary point.
--
--   **Formalization Note** The conclusion is the displayed condition (2.16). Its identification with $L_2(f)$-stationarity in the sense of Definition 2.3 goes through Lemma 2.2 and is not restated here. $L_2$ is universally quantified among constants satisfying (2.15). Assumption 2 is kept as on the page, although (2.15) is the hypothesis the proof uses. When $\|x^*\|_0<s$, $M_s(x^*)=0$ and the first line says $\nabla_i f(x^*)=0$ on $I_0(x^*)$.
-- source:
--   Beck, Eldar, Sparsity Constrained Nonlinear Optimization: Optimality Conditions and Algorithms, SIAM J. Optim. (2013), doi:10.1137/120869778 (source: arXiv:1203.4580v1), p. 12, Theorem 2.4, (2.16)

import Mathlib
import Definitions.Def_SparseNLO_CWOpt_Setting

namespace SparseNLO.CWOpt

/-- Theorem 2.4 (p. 12): under Assumption 2, every CW-minimum `x*` of (P) satisfies (2.16):
`|∇_i f(x*)| ≤ L2 · M_s(x*)` for `i ∈ I₀(x*)` and `∇_i f(x*) = 0` for `i ∈ I₁(x*)`,
where `L2` is any constant satisfying the local Lipschitz condition (2.15). -/
theorem theorem_2_4 {n s : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (hbdd : ∃ γ : ℝ, ∀ x, γ ≤ f x) (hs : 0 < s) (hsn : s < n)
    (Lf : NNReal) (hLf : LipschitzWith Lf (gradient f))
    (L2 : ℝ) (hL2 : LocalLipschitz f L2)
    (xstar : EuclideanSpace ℝ (Fin n)) (hcw : IsCWMin f s xstar) :
    (∀ i ∈ I0 xstar, |gradient f xstar i| ≤ L2 * Ms s xstar) ∧
      (∀ i ∈ I1 xstar, gradient f xstar i = 0) := by sorry

end SparseNLO.CWOpt
