-- Prove2me | Theorems.Thm_ProjReflGrad_Adaptive_lemma_4_3
-- name    : ProjReflGrad.Adaptive.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:15:22.890979+00:00
-- url     : https://prove2.me/theorems/87415047-67f7-4faa-986b-bcf1b74781a2
-- title:
--   Lemma 4.3, (4.5), p. 10 — the energy inequality of Algorithm 4.2 for z ∈ S
-- statement:
--   Let $H$ be a real Hilbert space, $C \subseteq H$ closed and convex, $F : H \to H$ monotone, $\alpha \in (0, \sqrt2 - 1)$, $\bar\lambda > 0$, and let $(x_n, y_n, \lambda_n, \tau_n)$ be a run of Algorithm 4.2. Let $z \in S$. Then for every $n \ge 1$
--   $$\|x_{n+1} - z\|^2 \le \|x_n - z\|^2 - (1 - \alpha(1+\sqrt2))\|x_n - y_n\|^2 - (1 - \sqrt2\alpha)\|x_{n+1} - y_n\|^2 + \alpha\|x_n - y_{n-1}\|^2 - 2\lambda_n\langle F(z), y_n - z\rangle. \qquad (4.5)$$
--
--   Here $y_n$ and $\lambda_n$ are the final values of iteration $n$, after any correction of step 4 (the paper's "for redefined values"). Inequality (4.5) is the analogue for Algorithm 4.2 of the energy inequality (3.1) of the constant-step method.
--
--   **Formalization Note** The statement assumes neither (C1) (a solution $z$ is given) nor the Lipschitz condition (C3): the proof uses only the inequalities built into the run (the ratio term of (4.1), (4.2), (4.4)), never $L$. The index range is $n \ge 1$, where $y_{n-1}$ and $\lambda_{n-1}$ are defined.
-- source:
--   Malitsky, Projected Reflected Gradient Methods for Monotone Variational Inequalities, arXiv:1502.04968v1, p. 10, Lemma 4.3, (4.5)

import Mathlib
import Definitions.Def_ProjReflGrad_Adaptive_Setting

namespace ProjReflGrad.Adaptive

/-- Lemma 4.3, (4.5) (Malitsky 2015, p. 10): along a run of Algorithm 4.2, for `z ∈ S` and
`α ∈ (0, √2 - 1)`, for every `n ≥ 1` (with the final, possibly corrected, `y_n`, `λ_n`)
`‖x_{n+1} - z‖² ≤ ‖x_n - z‖² - (1 - α(1 + √2))‖x_n - y_n‖² - (1 - √2α)‖x_{n+1} - y_n‖²
  + α‖x_n - y_{n-1}‖² - 2λ_n⟨F(z), y_n - z⟩`. -/
theorem lemma_4_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCcl : IsClosed C) (hCcv : Convex ℝ C) (F : H → H) (hC2 : ProjReflGrad.Weak.IsMonotoneMap F)
    (α lamInit lamBar : ℝ) (hα0 : 0 < α) (hα1 : α < Real.sqrt 2 - 1)
    (hlamBar : 0 < lamBar) (x y : ℕ → H) (lam tau : ℕ → ℝ)
    (hrun : IsAdaptiveRun C F α lamInit lamBar x y lam tau) (z : H) (hz : z ∈ ProjReflGrad.Weak.solSet C F) :
    ∀ n, 1 ≤ n →
      ‖x (n + 1) - z‖ ^ 2 ≤ ‖x n - z‖ ^ 2 - (1 - α * (1 + Real.sqrt 2)) * ‖x n - y n‖ ^ 2
        - (1 - Real.sqrt 2 * α) * ‖x (n + 1) - y n‖ ^ 2 + α * ‖x n - y (n - 1)‖ ^ 2
        - 2 * lam n * inner ℝ (F z) (y n - z) := by sorry

end ProjReflGrad.Adaptive
