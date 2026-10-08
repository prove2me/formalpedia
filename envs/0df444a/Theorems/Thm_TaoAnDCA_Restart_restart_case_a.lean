-- Prove2me | Theorems.Thm_TaoAnDCA_Restart_restart_case_a
-- name    : TaoAnDCA.Restart.restart_case_a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:58:46.619999+00:00
-- url     : https://prove2.me/theorems/1cd85425-8aed-436d-ae01-003f5019f0d2
-- title:
--   §4.2 case a), p. 492 — if ⟨b, x*⟩ > 0 then x̄ = −x* is feasible and f(x̄) = f(x*) − 2⟨b, x*⟩ < f(x*)
-- statement:
--   Let $A$ be a real symmetric $n\times n$ matrix, $b\in\mathbb R^n$, $r>0$, $f(x)=\tfrac12\langle x,Ax\rangle+\langle b,x\rangle$, and let $x^*$ be a Kuhn–Tucker point of $\min\{f(x):\|x\|\le r\}$ with multiplier $\lambda^*$. If $\langle b,x^*\rangle>0$, then $\bar x=-x^*$ satisfies $\|\bar x\|\le r$ and
--   $$f(\bar x)=f(x^*)+2\langle (A+\lambda^*I)x^*,x^*\rangle=f(x^*)-2\langle b,x^*\rangle<f(x^*).$$
--
--   This is the first case of the paper's construction of a starting point for restarting the DCA from a Kuhn–Tucker point that is not a global solution.
-- source:
--   Pham Dinh & Le Thi, A d.c. optimization algorithm for solving the trust-region subproblem, SIAM J. Optim. 8 (1998), p. 492, §4.2, "How to compute the initial point for restarting the DCA", case a)

import Mathlib
import Definitions.Def_TaoAnDCA_Restart_Setting

namespace TaoAnDCA.Restart

theorem restart_case_a {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r)
    (xs : EuclideanSpace ℝ (Fin n)) (lamStar : ℝ) (hkkt : TaoAnDCA.TRS.IsKKT A b r xs lamStar) (hb : 0 < inner ℝ b xs) :
    ‖-xs‖ ≤ r ∧
      TaoAnDCA.TRS.quad A b (-xs) = TaoAnDCA.TRS.quad A b xs + 2 * inner ℝ (A xs + lamStar • xs) xs ∧
      TaoAnDCA.TRS.quad A b xs + 2 * inner ℝ (A xs + lamStar • xs) xs = TaoAnDCA.TRS.quad A b xs - 2 * inner ℝ b xs ∧
      TaoAnDCA.TRS.quad A b (-xs) < TaoAnDCA.TRS.quad A b xs := by sorry

end TaoAnDCA.Restart
