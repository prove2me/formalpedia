-- Prove2me | Theorems.Thm_TaoAnDCA_Restart_restart_case_b1
-- name    : TaoAnDCA.Restart.restart_case_b1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:59:00.50424+00:00
-- url     : https://prove2.me/theorems/c0bc03ca-c919-48f6-8e80-e39660856069
-- title:
--   §4.2 case (b.1) and (23), p. 492 — x̄ = x* + γw with ‖x̄‖ = r, γ ≠ 0, has f(x̄) = f(x*) + (γ²/2)⟨w, (A + λ*I)w⟩ < f(x*)
-- statement:
--   Let $A$ be a real symmetric $n\times n$ matrix, $b\in\mathbb R^n$, $r>0$, $f(x)=\tfrac12\langle x,Ax\rangle+\langle b,x\rangle$, and let $x^*$ be a Kuhn–Tucker point of $\min\{f(x):\|x\|\le r\}$ with multiplier $\lambda^*$. Let $w\in\mathbb R^n$ be a direction of negative curvature, $\langle w,(A+\lambda^*I)w\rangle<0$, and assume that either $\|x^*\|<r$, or $\|x^*\|=r$ and $w^Tx^*\ne0$. Let $\gamma$ be given by (23),
--   $$\gamma=\begin{cases}-2(w^Tx^*)/\|w\|^2 & \text{if } \|x^*\|=r,\\ \bigl(-(w^Tx^*)\pm\sqrt\Delta\bigr)/\|w\|^2 & \text{if } \|x^*\|<r,\end{cases}\qquad \Delta=(w^Tx^*)^2-\|w\|^2(\|x^*\|^2-r^2),$$
--   with either choice of sign. Then $\gamma\ne0$, $\gamma$ solves $\|w\|^2\gamma^2+2w^Tx^*\gamma+\|x^*\|^2-r^2=0$, the point $\bar x=x^*+\gamma w$ satisfies $\|\bar x\|=r$, and
--   $$f(\bar x)=f(x^*)+\frac{\gamma^2}{2}\langle w,(A+\lambda^*I)w\rangle<f(x^*).$$
--
--   With $w=u$ an eigenvector for an eigenvalue $\lambda_1$ with $\lambda^*+\lambda_1<0$, (21) gives the curvature hypothesis and this is the paper's case (b.1); with $w=v$ from case (b.2) it is the paper's "Return to (b.1) with $v$ instead of $u$".
--
--   **Formalization Note** The statement is for a general direction $w$ with $\langle w,(A+\lambda^*I)w\rangle<0$ rather than for the eigenvector $u$, because case (b.2) applies it to a vector that is not an eigenvector. The heading "$\langle b,x^*\rangle\le0$" of case b) is not assumed: the computation of (b.1) does not use it, so the statement is stronger than the page. The sign $s=\pm1$ selects the root in (23).
-- source:
--   Pham Dinh & Le Thi, A d.c. optimization algorithm for solving the trust-region subproblem, SIAM J. Optim. 8 (1998), p. 492, §4.2, case (b.1), (23)

import Mathlib
import Definitions.Def_TaoAnDCA_Restart_Setting

namespace TaoAnDCA.Restart

theorem restart_case_b1 {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r)
    (xs : EuclideanSpace ℝ (Fin n)) (lamStar : ℝ) (hkkt : TaoAnDCA.TRS.IsKKT A b r xs lamStar)
    (w : EuclideanSpace ℝ (Fin n)) (hw : inner ℝ w (A w + lamStar • w) < 0)
    (hcase : ‖xs‖ < r ∨ (‖xs‖ = r ∧ inner ℝ w xs ≠ 0)) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    restartGamma w xs r s ≠ 0 ∧
      ‖w‖ ^ 2 * restartGamma w xs r s ^ 2 + 2 * inner ℝ w xs * restartGamma w xs r s
        + ‖xs‖ ^ 2 - r ^ 2 = 0 ∧
      ‖xs + restartGamma w xs r s • w‖ = r ∧
      TaoAnDCA.TRS.quad A b (xs + restartGamma w xs r s • w) =
        TaoAnDCA.TRS.quad A b xs + restartGamma w xs r s ^ 2 / 2 * inner ℝ w (A w + lamStar • w) ∧
      TaoAnDCA.TRS.quad A b (xs + restartGamma w xs r s • w) < TaoAnDCA.TRS.quad A b xs := by sorry

end TaoAnDCA.Restart
