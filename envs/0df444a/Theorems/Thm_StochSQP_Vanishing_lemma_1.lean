-- Prove2me | Theorems.Thm_StochSQP_Vanishing_lemma_1
-- name    : StochSQP.Vanishing.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:12.009198+00:00
-- url     : https://prove2.me/theorems/cd6f3701-fc06-4862-8935-886ae11c1f31
-- title:
--   Lemma 1, p. 11 — Cauchy-decrease constants κ_v, ω̲ for the normal step
-- statement:
--   Fix a problem $\min f(x)$ s.t. $c(x)=0$, valid parameters of Algorithm 1 and an open convex set $X$ on which Assumption 1 holds. There exist constants $\kappa_v > 0$ and $\underline\omega > 0$ such that, in any run of the algorithm whose iterates lie in $X$,
--   $$\|c_k\|_2\big(\|c_k\|_2 - \|c_k + J_k v_k\|_2\big) \ge \kappa_v \|J_k^T c_k\|_2^2 \quad\text{and}\quad \underline\omega\,\|J_k^T c_k\|_2^2 \le \|v_k\|_2 \le \omega \|J_k^T c_k\|_2$$
--   for all $k \in \mathbb N$ with $\|c_k\|_2 > 0$. Here $v_k$ is the normal step, $c_k = c(x_k)$ and $J_k = J(x_k)$.
--
--   The lemma quantifies the progress toward linearized feasibility made by any normal step satisfying the Cauchy decrease condition (6), and gives two-sided bounds on its length. The constants are uniform: they do not depend on the run.
--
--   **Formalization Note.** The constants are quantified before the run ("in any run of the algorithm"); they may depend on the problem, the parameters and the set $X$.
-- source:
--   Berahas, Curtis, O'Neill & Robinson, arXiv:2106.13015v2, p. 11, Lemma 1

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Model

open scoped InnerProductSpace RealInnerProductSpace

namespace StochSQP.Vanishing

theorem lemma_1 {n m : ℕ} (P : Problem n m) (A : Params) (hA : A.Valid)
    (X : Set (E n)) (hA1 : Assumption1 P A.L A.Γ X) :
    ∃ κv > (0 : ℝ), ∃ ωLow > (0 : ℝ), ∀ R : Run n m, IsRun P A R → (∀ k, R.x k ∈ X) →
      ∀ k : ℕ, 0 < ‖P.c (R.x k)‖ →
        κv * ‖P.Jt (R.x k) (P.c (R.x k))‖ ^ 2 ≤
            ‖P.c (R.x k)‖ * (‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.v k)‖) ∧
          ωLow * ‖P.Jt (R.x k) (P.c (R.x k))‖ ^ 2 ≤ ‖R.v k‖ ∧
          ‖R.v k‖ ≤ A.ω * ‖P.Jt (R.x k) (P.c (R.x k))‖ := by sorry

end StochSQP.Vanishing
