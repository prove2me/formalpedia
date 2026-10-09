-- Prove2me | Theorems.Thm_ProjReflGrad_Adaptive_eq_4_10
-- name    : ProjReflGrad.Adaptive.eq_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:15:30.071256+00:00
-- url     : https://prove2.me/theorems/f946aabd-1041-4fef-bbd0-d4e5ddecf0d0
-- title:
--   Proof of Theorem 4.4, (4.10), p. 12 — τ_nλ_n ≤ (1 + τ_{n−1})λ_{n−1} and the Lyapunov decrease (4.10)
-- statement:
--   Let $H$ be a real Hilbert space, $C \subseteq H$ closed and convex, $F : H \to H$ monotone, $\alpha \in (0, \sqrt2 - 1)$, $\bar\lambda > 0$, let $(x_n, y_n, \lambda_n, \tau_n)$ be a run of Algorithm 4.2 and $z \in S$. Then for every $n \ge 1$:
--
--   1. $\tau_n\lambda_n \le (1 + \tau_{n-1})\lambda_{n-1}$;
--   2. the inequality (4.10) holds:
--   $$\begin{aligned}\|x_{n+1} - z\|^2 + \alpha\|x_{n+1} - y_n\|^2 + 2\lambda_n(1+\tau_n)\langle F(z), x_n - z\rangle \le{}& \|x_n - z\|^2 + \alpha\|x_n - y_{n-1}\|^2 + 2\lambda_{n-1}(1+\tau_{n-1})\langle F(z), x_{n-1} - z\rangle \\ &- (1 - \alpha(1+\sqrt2))\big(\|x_n - y_n\|^2 + \|x_{n+1} - y_n\|^2\big).\end{aligned}$$
--
--   With $a_{n+1}$ the left-hand side and $b_n = (1 - \alpha(1+\sqrt2))(\|x_n - y_n\|^2 + \|x_{n+1} - y_n\|^2)$, (4.10) reads $a_{n+1} \le a_n - b_n$, the decrease that drives the convergence proof.
--
--   **Formalization Note** As for (4.5), neither (C1) nor (C3) is assumed. The index range is $n \ge 1$.
-- source:
--   Malitsky, Projected Reflected Gradient Methods for Monotone Variational Inequalities, arXiv:1502.04968v1, p. 12, proof of Theorem 4.4, (4.10)

import Mathlib
import Definitions.Def_ProjReflGrad_Adaptive_Setting

namespace ProjReflGrad.Adaptive

/-- Proof of Theorem 4.4, (4.10) (Malitsky 2015, p. 12): along a run of Algorithm 4.2 and for
`z ∈ S`, for every `n ≥ 1` one has `τ_n λ_n ≤ (1 + τ_{n-1}) λ_{n-1}` and
`‖x_{n+1} - z‖² + α‖x_{n+1} - y_n‖² + 2λ_n(1 + τ_n)⟨F(z), x_n - z⟩
  ≤ ‖x_n - z‖² + α‖x_n - y_{n-1}‖² + 2λ_{n-1}(1 + τ_{n-1})⟨F(z), x_{n-1} - z⟩
    - (1 - α(1 + √2))(‖x_n - y_n‖² + ‖x_{n+1} - y_n‖²)`. -/
theorem eq_4_10 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCcl : IsClosed C) (hCcv : Convex ℝ C) (F : H → H) (hC2 : ProjReflGrad.Weak.IsMonotoneMap F)
    (α lamInit lamBar : ℝ) (hα0 : 0 < α) (hα1 : α < Real.sqrt 2 - 1)
    (hlamBar : 0 < lamBar) (x y : ℕ → H) (lam tau : ℕ → ℝ)
    (hrun : IsAdaptiveRun C F α lamInit lamBar x y lam tau) (z : H) (hz : z ∈ ProjReflGrad.Weak.solSet C F) :
    (∀ n, 1 ≤ n → tau n * lam n ≤ (1 + tau (n - 1)) * lam (n - 1)) ∧
    ∀ n, 1 ≤ n →
      ‖x (n + 1) - z‖ ^ 2 + α * ‖x (n + 1) - y n‖ ^ 2
          + 2 * lam n * (1 + tau n) * inner ℝ (F z) (x n - z)
        ≤ ‖x n - z‖ ^ 2 + α * ‖x n - y (n - 1)‖ ^ 2
          + 2 * lam (n - 1) * (1 + tau (n - 1)) * inner ℝ (F z) (x (n - 1) - z)
          - (1 - α * (1 + Real.sqrt 2)) * (‖x n - y n‖ ^ 2 + ‖x (n + 1) - y n‖ ^ 2) := by sorry

end ProjReflGrad.Adaptive
