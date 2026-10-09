-- Prove2me | Theorems.Thm_ProjReflGrad_Adaptive_lam_le_lamBar
-- name    : ProjReflGrad.Adaptive.lam_le_lamBar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:15:32.525491+00:00
-- url     : https://prove2.me/theorems/e4712361-3dc3-4363-8be7-eed6fa5bb612
-- title:
--   Proof of Theorem 4.4, p. 12 — along every run 0 < λ_n ≤ λ̄ and τ_n ∈ (0, 1]
-- statement:
--   Let $H$ be a real Hilbert space, $C \subseteq H$ closed and convex, $F : H \to H$ $L$-Lipschitz with $L > 0$, $\alpha \in (0, \sqrt2 - 1)$, $\lambda_{-1} > 0$ and $\bar\lambda > 0$. For every run $(x_n, y_n, \lambda_n, \tau_n)$ of Algorithm 4.2 and every $n \ge 0$,
--   $$0 < \lambda_n \le \bar\lambda \qquad\text{and}\qquad 0 < \tau_n \le 1.$$
--
--   The proof of Theorem 4.4 recalls that $\bar\lambda$ is an upper bound of $(\lambda_n)$; positivity of $\lambda_n$ and $\tau_n \in (0,1]$ are what the step rule (4.1) and Lemma 4.2 presuppose at every step.
--
--   **Formalization Note** This item states only the upper bound and positivity. The paper also asserts that $\alpha/L$ is a lower bound of $(\lambda_n)$ "from Lemma 4.2"; that claim is not stated here (see the mission description).
-- source:
--   Malitsky, Projected Reflected Gradient Methods for Monotone Variational Inequalities, arXiv:1502.04968v1, p. 12, proof of Theorem 4.4

import Mathlib
import Definitions.Def_ProjReflGrad_Adaptive_Setting

namespace ProjReflGrad.Adaptive

/-- Proof of Theorem 4.4 (Malitsky 2015, p. 12): along every run of Algorithm 4.2 the step sizes
satisfy `0 < λ_n ≤ λ̄` and the reflection weights satisfy `τ_n ∈ (0, 1]`. -/
theorem lam_le_lamBar {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCcl : IsClosed C) (hCcv : Convex ℝ C) (F : H → H) (L : ℝ)
    (hL : 0 < L) (hC3 : ProjReflGrad.Weak.IsLipschitzMap F L)
    (α lamInit lamBar : ℝ) (hα0 : 0 < α) (hα1 : α < Real.sqrt 2 - 1) (hlamInit : 0 < lamInit)
    (hlamBar : 0 < lamBar) (x y : ℕ → H) (lam tau : ℕ → ℝ)
    (hrun : IsAdaptiveRun C F α lamInit lamBar x y lam tau) :
    ∀ n, 0 < lam n ∧ lam n ≤ lamBar ∧ 0 < tau n ∧ tau n ≤ 1 := by sorry

end ProjReflGrad.Adaptive
