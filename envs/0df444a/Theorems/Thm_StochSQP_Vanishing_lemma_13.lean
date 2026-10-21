-- Prove2me | Theorems.Thm_StochSQP_Vanishing_lemma_13
-- name    : StochSQP.Vanishing.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:46.997166+00:00
-- url     : https://prove2.me/theorems/43835b71-de67-49ee-8e06-f5a914dd4191
-- title:
--   Lemma 13, p. 19 — per-iteration decrease of the constraint violation when the merit parameter vanishes
-- statement:
--   Consider a run of Algorithm 1 under Assumption 1 (on an open convex set $X$ containing the iterates) and Assumption 3, and suppose Assumption 5 holds in this run: $\tau_k \to 0$ and $\|g_k - \nabla f(x_k)\|_2^2 \le M$ for all $k$, with $M > 0$. Suppose further that $\{\beta_k\}$ satisfies (28). Then for all $k \in \mathbb N$,
--   $$\|c_k\|_2 - \|c(x_k + \alpha_k d_k)\|_2 \ \ge\ \alpha_k\big(1 - (1-\eta)\beta_k\big)\Delta l(x_k,\tau_k,g_k,d_k) - \tau_k\big(f_k - f(x_k + \alpha_k d_k)\big) - \alpha_k\tau_k\big(\nabla f(x_k) - g_k\big)^T d_k ,$$
--   where $f_k = f(x_k)$.
--
--   This is the basic one-step inequality of the vanishing-merit-parameter analysis: the decrease in constraint violation is bounded below by the model reduction, up to an objective term weighted by $\tau_k$ and a gradient-error term.
--
--   **Formalization Note.** Assumption 5 is read pathwise. Its clause $\mathbb E_{k,\tau,\rm zero}[g_k] = \nabla f(x_k)$ (unbiasedness conditional on the event $\{\tau_k\} \searrow 0$) is a probabilistic statement and is dropped; the remaining clauses are kept as hypotheses as printed. That $\{\tau_k\}$ is nonincreasing follows from the run and is not assumed.
-- source:
--   Berahas, Curtis, O'Neill & Robinson, arXiv:2106.13015v2, p. 19, Lemma 13 (Assumption 5, p. 19)

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Model

open scoped InnerProductSpace RealInnerProductSpace

namespace StochSQP.Vanishing

theorem lemma_13 {n m : ℕ} (P : Problem n m) (A : Params) (hA : A.Valid)
    (X : Set (E n)) (hA1 : Assumption1 P A.L A.Γ X)
    (R : Run n m) (hR : IsRun P A R) (hX : ∀ k, R.x k ∈ X)
    (κH ζH : ℝ) (hA3 : Assumption3 P R κH ζH)
    (M : ℝ) (hM : 0 < M) (hg : ∀ k, ‖R.g k - P.grad (R.x k)‖ ^ 2 ≤ M)
    (hτ : Filter.Tendsto R.τ Filter.atTop (nhds 0))
    (h28 : Cond28 A R) :
    ∀ k : ℕ, R.α k * (1 - (1 - A.η) * R.β k) * deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) -
        R.τ k * (P.f (R.x k) - P.f (R.x k + R.α k • R.d k)) -
        R.α k * R.τ k * ⟪P.grad (R.x k) - R.g k, R.d k⟫_ℝ ≤
      ‖P.c (R.x k)‖ - ‖P.c (R.x k + R.α k • R.d k)‖ := by sorry

end StochSQP.Vanishing
