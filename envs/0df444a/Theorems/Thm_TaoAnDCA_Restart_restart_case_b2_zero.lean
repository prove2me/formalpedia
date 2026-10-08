-- Prove2me | Theorems.Thm_TaoAnDCA_Restart_restart_case_b2_zero
-- name    : TaoAnDCA.Restart.restart_case_b2_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:58:29.803514+00:00
-- url     : https://prove2.me/theorems/67207727-a8f1-4c67-8f8d-780a41603674
-- title:
--   §4.2 case (b.2), first bullet, p. 493 — if bᵀx* = 0, v = u + τx* has vᵀx* ≠ 0 and vᵀ(A + λ*I)v < 0 for the stated τ < 0
-- statement:
--   Let $A$ be a real symmetric $n\times n$ matrix, $b\in\mathbb R^n$, $r>0$, and let $x^*$ be a Kuhn–Tucker point of $\min\{\tfrac12\langle x,Ax\rangle+\langle b,x\rangle:\|x\|\le r\}$ with multiplier $\lambda^*$ and $\|x^*\|=r$. Let $u\in\mathbb R^n$ satisfy $u^T(A+\lambda^*I)u<0$ and $u^Tx^*=0$, assume $b^Tx^*=0$, and put $v=u+\tau x^*$. Then:
--
--   1. if $b^Tu\le0$, then $v^Tx^*\ne0$ and $v^T(A+\lambda^*I)v<0$ for every $\tau<0$;
--   2. if $b^Tu>0$, then $v^Tx^*\ne0$ and $v^T(A+\lambda^*I)v<0$ for every $\tau$ with
--   $$0>\tau>\frac{u^T(A+\lambda^*I)u}{2\,b^Tu}.$$
--
--   Such a $v$ is the direction with which case (b.1) is re-entered when $\|x^*\|=r$ and $u^Tx^*=0$.
--
--   **Formalization Note** The page prints the range in item 2 as $0>\tau>u^T(A+\lambda^*I)u/b^Tu$, without the factor $2$. With $b^Tx^*=0$ the curvature is $-2\tau\,b^Tu+u^T(A+\lambda^*I)u$, so the correct bound carries the factor 2, and the printed range is false for a general $u$ (take $u^T(A+\lambda^*I)u=-1$, $b^Tu=1$, $\tau=-0.9$: the curvature is $+0.8$). The statement uses the corrected bound. It takes a general $u$ with negative curvature rather than the eigenvector of §4.2: for an eigenvector $u$ with $u^Tx^*=0$ one has $b^Tu=-(\lambda_1+\lambda^*)u^Tx^*=0$, so item 2 would be vacuous.
-- source:
--   Pham Dinh & Le Thi, A d.c. optimization algorithm for solving the trust-region subproblem, SIAM J. Optim. 8 (1998), p. 493, §4.2, case (b.2), first bullet

import Mathlib
import Definitions.Def_TaoAnDCA_Restart_Setting

namespace TaoAnDCA.Restart

theorem restart_case_b2_zero {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r)
    (xs : EuclideanSpace ℝ (Fin n)) (lamStar : ℝ) (hkkt : TaoAnDCA.TRS.IsKKT A b r xs lamStar) (hnorm : ‖xs‖ = r)
    (u : EuclideanSpace ℝ (Fin n)) (hu : inner ℝ u (A u + lamStar • u) < 0) (hux : inner ℝ u xs = 0)
    (hb : inner ℝ b xs = 0) :
    (inner ℝ b u ≤ 0 → ∀ τ : ℝ, τ < 0 →
        inner ℝ (u + τ • xs) xs ≠ 0 ∧
          inner ℝ (u + τ • xs) (A (u + τ • xs) + lamStar • (u + τ • xs)) < 0) ∧
      (0 < inner ℝ b u → ∀ τ : ℝ, inner ℝ u (A u + lamStar • u) / (2 * inner ℝ b u) < τ → τ < 0 →
        inner ℝ (u + τ • xs) xs ≠ 0 ∧
          inner ℝ (u + τ • xs) (A (u + τ • xs) + lamStar • (u + τ • xs)) < 0) := by sorry

end TaoAnDCA.Restart
