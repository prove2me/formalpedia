-- Prove2me | Theorems.Thm_StochSQP_Vanishing_lemma_3
-- name    : StochSQP.Vanishing.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:38.264994+00:00
-- url     : https://prove2.me/theorems/295c4da7-b00d-407f-9dec-ceb8153595e2
-- title:
--   Lemma 3, p. 12 — ξ_k is eventually constant and bounded below by ξ_min
-- statement:
--   Fix a problem, valid parameters, an open convex set $X$ on which Assumption 1 holds, and the constants $\kappa_H, \zeta$ of Assumption 3. There exists $\xi_{\min} > 0$ such that, in any run whose iterates lie in $X$ and whose matrices $H_k$ satisfy Assumption 3 with $\kappa_H, \zeta$, there is $k_\xi \in \mathbb N$ with
--   $$\xi_k = \xi_{k_\xi} \ \text{ for all } k \ge k_\xi, \qquad \xi_{k_\xi} \in [\xi_{\min}, \infty).$$
--
--   The step-size parameter $\xi_k$, which estimates a lower bound for the ratio of the model reduction to the squared length of the search direction, is therefore bounded away from zero deterministically, uniformly over runs.
--
--   **Formalization Note.** The constant is quantified before the run.
-- source:
--   Berahas, Curtis, O'Neill & Robinson, arXiv:2106.13015v2, p. 12, Lemma 3

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Model

open scoped InnerProductSpace RealInnerProductSpace

namespace StochSQP.Vanishing

theorem lemma_3 {n m : ℕ} (P : Problem n m) (A : Params) (hA : A.Valid)
    (X : Set (E n)) (hA1 : Assumption1 P A.L A.Γ X)
    (κH ζH : ℝ) :
    ∃ ξmin > (0 : ℝ), ∀ R : Run n m, IsRun P A R → (∀ k, R.x k ∈ X) →
      Assumption3 P R κH ζH →
        ∃ K : ℕ, (∀ k ≥ K, R.ξ k = R.ξ K) ∧ ξmin ≤ R.ξ K := by sorry

end StochSQP.Vanishing
