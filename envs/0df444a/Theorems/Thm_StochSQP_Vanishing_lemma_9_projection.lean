-- Prove2me | Theorems.Thm_StochSQP_Vanishing_lemma_9_projection
-- name    : StochSQP.Vanishing.lemma_9_projection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:45.703984+00:00
-- url     : https://prove2.me/theorems/32d58ac9-f5a8-4b08-931e-04e15f9c096f
-- title:
--   Proof of Lemma 9, p. 15 — under (28), α_k ∈ (0, 1] and the projection (22) never sets α_k > α_k^suff
-- statement:
--   Consider a run of Algorithm 1 under Assumption 1 (on an open convex set $X$ containing the iterates) and Assumption 3, and suppose that $\{\beta_k\}$ satisfies condition (28):
--   $$\beta_k \in (0,1] \quad\text{and}\quad \frac{2(1-\eta)\beta_k\xi_k\max\{\tau_k,1\}}{\tau_k L + \Gamma} \in (0,1] \quad \text{for all } k \in \mathbb N .$$
--   Then for every $k$, the step size satisfies $\alpha_k \in (0,1]$, and if $d_k \neq 0$ then
--   $$\alpha_k \le \alpha_k^{\rm suff} = \min\Big\{\frac{2(1-\eta)\beta_k\,\Delta l(x_k,\tau_k,g_k,d_k)}{(\tau_k L + \Gamma)\|d_k\|_2^2}, 1\Big\},$$
--   that is, the projection (22) onto the safeguard interval never increases the trial step size.
--
--   These two facts are stated in the proof of Lemma 9 and reused in the proof of Lemma 13.
--
--   **Formalization Note.** When $d_k = 0$ the algorithm sets $\alpha_k = 1$ and $\alpha_k^{\rm suff}$ is not computed, so the comparison with $\alpha_k^{\rm suff}$ is stated for $d_k \neq 0$.
-- source:
--   Berahas, Curtis, O'Neill & Robinson, arXiv:2106.13015v2, p. 15, proof of Lemma 9

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Model

open scoped InnerProductSpace RealInnerProductSpace

namespace StochSQP.Vanishing

theorem lemma_9_projection {n m : ℕ} (P : Problem n m) (A : Params) (hA : A.Valid)
    (X : Set (E n)) (hA1 : Assumption1 P A.L A.Γ X)
    (R : Run n m) (hR : IsRun P A R) (hX : ∀ k, R.x k ∈ X)
    (κH ζH : ℝ) (hA3 : Assumption3 P R κH ζH)
    (h28 : Cond28 A R) :
    ∀ k : ℕ, 0 < R.α k ∧ R.α k ≤ 1 ∧ (R.d k ≠ 0 → R.α k ≤ alphaSuff P A R k) := by sorry

end StochSQP.Vanishing
