-- Prove2me | Theorems.Thm_StochSQP_Vanishing_lemma_14
-- name    : StochSQP.Vanishing.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:40.608487+00:00
-- url     : https://prove2.me/theorems/1828b5b4-1b75-44d3-8b50-f48c55a3d696
-- title:
--   Lemma 14, p. 19 — bound on the gradient-error term α_kτ_k(∇f(x_k) − g_k)ᵀd_k
-- statement:
--   Consider a run of Algorithm 1 under Assumption 1 (on an open convex set $X$ containing the iterates) and Assumption 3, in which Assumption 5 holds: $\tau_k \to 0$ and $\|g_k - \nabla f(x_k)\|_2^2 \le M$ for all $k$, with $M > 0$. Then there exists $\kappa_\beta > 0$ such that
--   $$\alpha_k\tau_k(\nabla f(x_k) - g_k)^T d_k \le \begin{cases} \beta_k\tau_k\kappa_\beta & \text{for all } k \text{ with } \|u_k\|_2^2 < \chi_k\|v_k\|_2^2, \\ \beta_k\tau_k\max\{\beta_k,\tau_k\}\kappa_\beta & \text{for all } k \text{ with } \|u_k\|_2^2 \ge \chi_k\|v_k\|_2^2 . \end{cases}$$
--
--   The lemma bounds the last term of Lemma 13, separately for normally and tangentially dominated search directions.
--
--   **Formalization Note.** $\kappa_\beta$ may depend on the run ("For any run …, there exists"). Assumption 5 is read pathwise, without its unbiasedness clause (see Lemma 13).
-- source:
--   Berahas, Curtis, O'Neill & Robinson, arXiv:2106.13015v2, p. 19, Lemma 14

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Model

open scoped InnerProductSpace RealInnerProductSpace

namespace StochSQP.Vanishing

theorem lemma_14 {n m : ℕ} (P : Problem n m) (A : Params) (hA : A.Valid)
    (X : Set (E n)) (hA1 : Assumption1 P A.L A.Γ X)
    (R : Run n m) (hR : IsRun P A R) (hX : ∀ k, R.x k ∈ X)
    (κH ζH : ℝ) (hA3 : Assumption3 P R κH ζH)
    (M : ℝ) (hM : 0 < M) (hg : ∀ k, ‖R.g k - P.grad (R.x k)‖ ^ 2 ≤ M)
    (hτ : Filter.Tendsto R.τ Filter.atTop (nhds 0)) :
    ∃ κβ > (0 : ℝ), ∀ k : ℕ,
      (¬ R.TangDom k →
        R.α k * R.τ k * ⟪P.grad (R.x k) - R.g k, R.d k⟫_ℝ ≤ R.β k * R.τ k * κβ) ∧
      (R.TangDom k →
        R.α k * R.τ k * ⟪P.grad (R.x k) - R.g k, R.d k⟫_ℝ ≤
          R.β k * R.τ k * max (R.β k) (R.τ k) * κβ) := by sorry

end StochSQP.Vanishing
