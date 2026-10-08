-- Prove2me | Theorems.Thm_RobustUncLP_Ellipsoidal_cqp_duality
-- name    : RobustUncLP.Ellipsoidal.cqp_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T12:29:54.16543+00:00
-- url     : https://prove2.me/theorems/dfaf74c0-b378-4c8a-a568-971e864662d1
-- title:
--   Appendix, (II), p. 15 — conic quadratic duality: strictly feasible and bounded below ⇒ dual solvable, equal values
-- statement:
--   Consider the conic quadratic problem (CQP$_p$) and its dual (CQP$_d$). Suppose that:
--
--   1. (CQP$_p$) is **strictly feasible**: some $\hat z$ satisfies $R\hat z = r$ and $\|A_\ell\hat z - b_\ell\| < c_\ell^T\hat z - d_\ell$ for every $\ell = 0, \dots, k$;
--   2. the objective $e^Tz + \varphi$ is bounded below on the feasible set of (CQP$_p$).
--
--   Then there is a real number $v$ which is the infimum of the primal objective over the primal feasible set, and which is attained as the maximum of the dual objective over the dual feasible set:
--   $$v = \inf_{z \text{ feasible}} (e^Tz + \varphi) = \max_{(\lambda,\mu,\nu) \text{ feasible}} \Big( r^T\lambda + \sum_{\ell=0}^k [d_\ell\nu_\ell + b_\ell^T\mu_\ell] + \varphi \Big).$$
--
--   The paper quotes this from Nesterov and Nemirovski (1994), Theorem 4.2.1, and applies it to each problem $(P_i[x])$.
--
--   **Formalization Note** "The dual is solvable and the optimal values are equal" is encoded as `IsGLB` of the primal objective values together with `IsGreatest` of the dual objective values at the same $v$. The dual uses the sum over $\ell = 0, \dots, k$ in its equality constraint (see the `CQP` definition). The rows of $R$ need not be linearly independent.
-- source:
--   Ben-Tal & Nemirovski, Robust solutions of uncertain linear programs, Oper. Res. Lett. 25 (1999); authors' manuscript, Appendix, p. 15, claim (II) (citing Nesterov–Nemirovski 1994, Thm 4.2.1)

import Mathlib
import Definitions.Def_RobustUncLP_Ellipsoidal_Setting
import Definitions.Def_RobustUncLP_Ellipsoidal_CQP

namespace RobustUncLP.Ellipsoidal

open Matrix CQPData

/-- Appendix, claim (II), p. 15 (conic quadratic duality, cited from Nesterov–Nemirovski 1994,
Theorem 4.2.1): if `(CQP_p)` is strictly feasible and its objective is bounded below on its
feasible set, then `(CQP_d)` is solvable and the two optimal values coincide. -/
theorem cqp_duality {N p k : ℕ} (P : CQPData N p k)
    (hstrict : ∃ z, P.R *ᵥ z = P.r ∧ ∀ ℓ, euclidNorm (P.A ℓ *ᵥ z - P.b ℓ) < P.c ℓ ⬝ᵥ z - P.d ℓ)
    (hbdd : BddBelow (P.primalObj '' P.primalFeas)) :
    ∃ v : ℝ, IsGLB (P.primalObj '' P.primalFeas) v ∧ IsGreatest (P.dualObj '' P.dualFeas) v := by sorry

end RobustUncLP.Ellipsoidal
