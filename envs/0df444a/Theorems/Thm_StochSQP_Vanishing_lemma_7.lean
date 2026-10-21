-- Prove2me | Theorems.Thm_StochSQP_Vanishing_lemma_7
-- name    : StochSQP.Vanishing.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:32.175889+00:00
-- url     : https://prove2.me/theorems/bd26e33a-2284-4c72-9de5-687827e36c0c
-- title:
--   Lemma 7, p. 13 — bounded gradient errors give bounded tangential steps
-- statement:
--   Consider a run of Algorithm 1 under Assumption 1 (on an open convex set $X$ containing the iterates) and Assumption 3. If the sequence $\{\|g_k - \nabla f(x_k)\|_2\}$ is bounded by a positive real number $\kappa_g$, then there is a positive real number $\kappa_u$ with
--   $$\|u_k\|_2 \le \kappa_u \quad\text{for all } k \in \mathbb N .$$
--
--   Here $u_k$ is the tangential component of the search direction, computed from the linear system (9) with the stochastic gradient $g_k$. The lemma converts a deterministic bound on the gradient error into a bound on the search directions.
--
--   **Formalization Note.** The constant $\kappa_u$ may depend on the run.
-- source:
--   Berahas, Curtis, O'Neill & Robinson, arXiv:2106.13015v2, p. 13, Lemma 7

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Model

open scoped InnerProductSpace RealInnerProductSpace

namespace StochSQP.Vanishing

theorem lemma_7 {n m : ℕ} (P : Problem n m) (A : Params) (hA : A.Valid)
    (X : Set (E n)) (hA1 : Assumption1 P A.L A.Γ X)
    (R : Run n m) (hR : IsRun P A R) (hX : ∀ k, R.x k ∈ X)
    (κH ζH : ℝ) (hA3 : Assumption3 P R κH ζH)
    (κg : ℝ) (hκg : 0 < κg) (hg : ∀ k, ‖R.g k - P.grad (R.x k)‖ ≤ κg) :
    ∃ κu > (0 : ℝ), ∀ k : ℕ, ‖R.u k‖ ≤ κu := by sorry

end StochSQP.Vanishing
