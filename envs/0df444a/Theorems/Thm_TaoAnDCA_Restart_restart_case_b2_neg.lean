-- Prove2me | Theorems.Thm_TaoAnDCA_Restart_restart_case_b2_neg
-- name    : TaoAnDCA.Restart.restart_case_b2_neg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:58:41.965391+00:00
-- url     : https://prove2.me/theorems/3e7a712e-07cf-414f-b924-79c1dee0df10
-- title:
--   §4.2 case (b.2), second bullet, p. 493 — if bᵀx* < 0, v = u + τx* has vᵀx* ≠ 0 and vᵀ(A + λ*I)v < 0 for τ₁ < τ < 0
-- statement:
--   Let $A$ be a real symmetric $n\times n$ matrix, $b\in\mathbb R^n$, $r>0$, and let $x^*$ be a Kuhn–Tucker point of $\min\{\tfrac12\langle x,Ax\rangle+\langle b,x\rangle:\|x\|\le r\}$ with multiplier $\lambda^*$ and $\|x^*\|=r$. Let $u\in\mathbb R^n$ satisfy $u^T(A+\lambda^*I)u<0$ and $u^Tx^*=0$, and assume $b^Tx^*<0$. Let
--   $$\tau_1=\frac{\sqrt{(b^Tu)^2+b^Tx^*\,u^T(A+\lambda^*I)u}-b^Tu}{b^Tx^*}.$$
--   Then $\tau_1<0$, $\tau_1$ is the smallest root of the polynomial $-b^Tx^*\tau^2-2b^Tu\,\tau+u^T(A+\lambda^*I)u$, and for every $\tau$ with $\tau_1<\tau<0$ the vector $v=u+\tau x^*$ satisfies $v^Tx^*\ne0$ and $v^T(A+\lambda^*I)v<0$.
--
--   Together with the first bullet this supplies, when $\|x^*\|=r$ and $u^Tx^*=0$, a direction with which case (b.1) is re-entered.
--
--   **Formalization Note** The page defines $\tau_1$ as "the smallest root of the second degree polynomial" and then prints $\tau_1=[b^Tu+((b^Tu)^2+b^Tx^*u^T(A+\lambda^*I)u]^{1/2})]/b^Tx^*$, with unbalanced brackets and the sign of $b^Tu$ reversed. The statement uses the smallest root, which is the formula above (check: $b^Tx^*=-1$, $b^Tu=1$, $u^T(A+\lambda^*I)u=-1$ gives roots $1\pm\sqrt2$, smallest $1-\sqrt2$, while the printed formula gives $-1-\sqrt2$). The two agree when $b^Tu=0$, the case of an eigenvector $u$. The radicand is positive under the hypotheses. As in the first bullet, $u$ is a general vector of negative curvature.
-- source:
--   Pham Dinh & Le Thi, A d.c. optimization algorithm for solving the trust-region subproblem, SIAM J. Optim. 8 (1998), p. 493, §4.2, case (b.2), second bullet

import Mathlib
import Definitions.Def_TaoAnDCA_Restart_Setting

namespace TaoAnDCA.Restart

theorem restart_case_b2_neg {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r)
    (xs : EuclideanSpace ℝ (Fin n)) (lamStar : ℝ) (hkkt : TaoAnDCA.TRS.IsKKT A b r xs lamStar) (hnorm : ‖xs‖ = r)
    (u : EuclideanSpace ℝ (Fin n)) (hu : inner ℝ u (A u + lamStar • u) < 0) (hux : inner ℝ u xs = 0)
    (hb : inner ℝ b xs < 0) :
    let τ₁ : ℝ := (Real.sqrt (inner ℝ b u ^ 2 + inner ℝ b xs * inner ℝ u (A u + lamStar • u))
      - inner ℝ b u) / inner ℝ b xs
    τ₁ < 0 ∧
      -(inner ℝ b xs) * τ₁ ^ 2 - 2 * inner ℝ b u * τ₁ + inner ℝ u (A u + lamStar • u) = 0 ∧
      (∀ τ : ℝ, -(inner ℝ b xs) * τ ^ 2 - 2 * inner ℝ b u * τ + inner ℝ u (A u + lamStar • u) = 0 →
        τ₁ ≤ τ) ∧
      ∀ τ : ℝ, τ₁ < τ → τ < 0 →
        inner ℝ (u + τ • xs) xs ≠ 0 ∧
          inner ℝ (u + τ • xs) (A (u + τ • xs) + lamStar • (u + τ • xs)) < 0 := by sorry

end TaoAnDCA.Restart
