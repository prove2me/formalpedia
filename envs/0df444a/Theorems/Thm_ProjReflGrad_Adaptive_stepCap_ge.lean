-- Prove2me | Theorems.Thm_ProjReflGrad_Adaptive_stepCap_ge
-- name    : ProjReflGrad.Adaptive.stepCap_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:15:42.399722+00:00
-- url     : https://prove2.me/theorems/92191193-a69c-4f33-b1f8-e9ccefb275fe
-- title:
--   Proof of Lemma 4.2, pp. 9–10 — the step rule λ(y, τ) is at least α/L
-- statement:
--   Let $F : H \to H$ be $L$-Lipschitz with $L > 0$ and let $\alpha > 0$. Let $\lambda(\cdot,\cdot)$ be the step rule (4.1) for the previous data $y_{n-1}$, $\tau_{n-1} \ge 0$, $\lambda_{n-1}$ and cap $\bar\lambda$. If $\lambda_{n-1} \ge \alpha/L$ and $\bar\lambda \ge \alpha/L$, then for every $y \in H$ and every $\tau \in (0, 1]$
--   $$\lambda(y, \tau) \ge \frac{\alpha}{L}.$$
--
--   This is the first claim of the proof of Lemma 4.2, used there to show that $\tau'_n = \alpha/(\lambda_{n-1}L)$ satisfies (4.3).
--
--   **Formalization Note** The two hypotheses $\lambda_{n-1} \ge \alpha/L$ and $\bar\lambda \ge \alpha/L$ are made explicit. The first is the induction hypothesis of the paper's argument ("Then $\lambda_0 \ge \alpha/L$ and hence by induction"); the second is the reading of "some large $\bar\lambda > 0$" (Algorithm 4.2, step 1) that this argument needs. Neither is assumed in the goal theorem.
-- source:
--   Malitsky, Projected Reflected Gradient Methods for Monotone Variational Inequalities, arXiv:1502.04968v1, pp. 9–10, proof of Lemma 4.2

import Mathlib
import Definitions.Def_ProjReflGrad_Adaptive_Setting

namespace ProjReflGrad.Adaptive

/-- Proof of Lemma 4.2 (Malitsky 2015, pp. 9–10): for an `L`-Lipschitz `F`, `λ(y, τ) ≥ α/L` for all
`y`, `y_{n-1}` and `τ ∈ (0, 1]`, provided `λ_{n-1} ≥ α/L` (the induction hypothesis) and
`λ̄ ≥ α/L` (the reading of "some large `λ̄`" the proof uses). -/
theorem stepCap_ge {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (F : H → H) (L : ℝ) (hL : 0 < L)
    (hC3 : ProjReflGrad.Weak.IsLipschitzMap F L) (α lamBar : ℝ) (hα : 0 < α) (yp y : H) (taup lamp tau : ℝ)
    (htaup : 0 ≤ taup) (htau : tau ∈ Set.Ioc 0 1) (hlamp : α / L ≤ lamp)
    (hbar : α / L ≤ lamBar) :
    α / L ≤ stepCap F α lamBar yp taup lamp y tau := by sorry

end ProjReflGrad.Adaptive
