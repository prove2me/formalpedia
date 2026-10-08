-- Prove2me | Theorems.Thm_TaoAnDCA_Restart_restart_exists
-- name    : TaoAnDCA.Restart.restart_exists
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:58:26.419457+00:00
-- url     : https://prove2.me/theorems/c18c5ab3-c39b-454e-80a1-b0e5a32ce175
-- title:
--   §4.2 "Summing up", p. 493 — a Kuhn–Tucker point x* with an eigenpair (λ₁, u), λ* + λ₁ < 0, admits x̄ with ‖x̄‖ ≤ r and f(x̄) < f(x*)
-- statement:
--   Let $A$ be a real symmetric $n\times n$ matrix, $b\in\mathbb R^n$, $r>0$, and $f(x)=\tfrac12\langle x,Ax\rangle+\langle b,x\rangle$. Let $x^*$ be a Kuhn–Tucker point of the trust-region subproblem $\min\{f(x):\|x\|\le r\}$ with multiplier $\lambda^*$: $\lambda^*\ge0$, $(A+\lambda^*I)x^*=-b$, $\lambda^*(\|x^*\|-r)=0$, $\|x^*\|\le r$. Let $u\ne0$ be an eigenvector of $A$, $Au=\lambda_1u$, with
--   $$\lambda^*+\lambda_1<0 .$$
--   Then there exists $\bar x\in\mathbb R^n$ with
--   $$\|\bar x\|\le r\qquad\text{and}\qquad f(\bar x)<f(x^*).$$
--
--   In §4.2 the condition $\lambda^*+\lambda_1<0$, with $\lambda_1$ the smallest eigenvalue of $A$, is the test that detects a Kuhn–Tucker point which is not a global solution; this theorem says that such a point can always be improved, so the DCA can be restarted from a strictly better feasible point. That is the basis of the paper's global algorithm GDCA.
--
--   **Formalization Note** The page speaks of the smallest eigenvalue $\lambda_1$ and of a point "produced by the DCA"; neither is used, so the statement holds for every Kuhn–Tucker point and every eigenpair with $\lambda^*+\lambda_1<0$, which is stronger. The hypothesis is the paper's test $\lambda^*+\lambda_1<0$, not "$x^*$ is not a global solution", which would make the conclusion a restatement of the hypothesis.
-- source:
--   Pham Dinh & Le Thi, A d.c. optimization algorithm for solving the trust-region subproblem, SIAM J. Optim. 8 (1998), p. 493, §4.2, "Summing up" (with (21), p. 491)

import Mathlib
import Definitions.Def_TaoAnDCA_Restart_Setting

namespace TaoAnDCA.Restart

theorem restart_exists {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r)
    (xs : EuclideanSpace ℝ (Fin n)) (lamStar : ℝ) (hkkt : TaoAnDCA.TRS.IsKKT A b r xs lamStar)
    (lam1 : ℝ) (u : EuclideanSpace ℝ (Fin n)) (hu : u ≠ 0) (hAu : A u = lam1 • u) (hneg : lamStar + lam1 < 0) :
    ∃ xbar : EuclideanSpace ℝ (Fin n), ‖xbar‖ ≤ r ∧ TaoAnDCA.TRS.quad A b xbar < TaoAnDCA.TRS.quad A b xs := by sorry

end TaoAnDCA.Restart
