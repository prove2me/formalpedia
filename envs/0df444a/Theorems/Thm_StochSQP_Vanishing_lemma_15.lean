-- Prove2me | Theorems.Thm_StochSQP_Vanishing_lemma_15
-- name    : StochSQP.Vanishing.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:47.033288+00:00
-- url     : https://prove2.me/theorems/571fa371-8214-4fd0-b5c6-4a11d0c8c80b
-- title:
--   Lemma 15, p. 20 — lower bounds on the step size α_k for normally and tangentially dominated directions
-- statement:
--   Consider a run of Algorithm 1 under Assumption 1 (on an open convex set $X$ containing the iterates) and Assumption 3, in which Assumption 5 holds ($\tau_k \to 0$ and $\|g_k - \nabla f(x_k)\|_2^2 \le M$ for all $k$, with $M > 0$). For $\gamma > 0$ let $\mathcal X_\gamma = \{x \in \mathbb R^n : \|J(x)^T c(x)\|_2 \ge \gamma\}$. Then:
--   1. there exists $\underline\alpha > 0$ such that $\alpha_k \ge \underline\alpha\,\beta_k$ for each $k$ with $\|u_k\|_2^2 < \chi_k\|v_k\|_2^2$;
--   2. there is a constant $C>0$, independent of $\gamma$, such that for each $\gamma > 0$ one may take $\epsilon_\gamma=C\gamma^2$ and, whenever $\|u_k\|_2^2 \ge \chi_k\|v_k\|_2^2$,
--   $$x_k \in \mathcal X_\gamma \implies \alpha_k \ge \min\{C\gamma^2\beta_k,\ C\gamma^2\beta_k\tau_k + \theta\beta_k^2\}.$$
--
--   The step size of a normally dominated direction stays proportional to $\beta_k$ even when the merit parameter vanishes, while for tangentially dominated directions away from stationary points of the infeasibility measure it is bounded below in terms of $\beta_k$, $\tau_k$ and $\theta$.
--
--   **Formalization Note.** The coefficient $C$ is quantified before $\gamma$, expressing the paper's "proportional to $\gamma^2$" claim. The displayed coefficient in the paper's proof has order $\gamma^4$ near zero, so the printed derivation alone does not establish this stronger bound. Lemma 15 is stated in §4.2, which makes Assumption 5 throughout; it is read pathwise without its unbiasedness clause. The constants may depend on the run.
-- source:
--   Berahas, Curtis, O'Neill & Robinson, arXiv:2106.13015v2, p. 20, Lemma 15, (32)

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Model

open scoped InnerProductSpace RealInnerProductSpace

namespace StochSQP.Vanishing

theorem lemma_15 {n m : ℕ} (P : Problem n m) (A : Params) (hA : A.Valid)
    (X : Set (E n)) (hA1 : Assumption1 P A.L A.Γ X)
    (R : Run n m) (hR : IsRun P A R) (hX : ∀ k, R.x k ∈ X)
    (κH ζH : ℝ) (hA3 : Assumption3 P R κH ζH)
    (M : ℝ) (hM : 0 < M) (hg : ∀ k, ‖R.g k - P.grad (R.x k)‖ ^ 2 ≤ M)
    (hτ : Filter.Tendsto R.τ Filter.atTop (nhds 0)) :
    (∃ αLow > (0 : ℝ), ∀ k : ℕ, ¬ R.TangDom k → αLow * R.β k ≤ R.α k) ∧
    (∃ C > (0 : ℝ), ∀ γ > (0 : ℝ), ∀ k : ℕ,
      γ ≤ ‖P.Jt (R.x k) (P.c (R.x k))‖ → R.TangDom k →
        min ((C * γ ^ 2) * R.β k)
          ((C * γ ^ 2) * R.β k * R.τ k + A.θ * R.β k ^ 2) ≤ R.α k) := by sorry

end StochSQP.Vanishing
