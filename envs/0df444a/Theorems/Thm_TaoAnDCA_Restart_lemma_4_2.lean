-- Prove2me | Theorems.Thm_TaoAnDCA_Restart_lemma_4_2
-- name    : TaoAnDCA.Restart.lemma_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:58:39.397975+00:00
-- url     : https://prove2.me/theorems/a231e663-6aa9-4106-b681-4150bda3effe
-- title:
--   Lemma 4.2, p. 492 — if (A + μI)y = −b then f(x) = f(y) − (μ/2)(‖x‖² − ‖y‖²) + ½⟨x − y, (A + μI)(x − y)⟩
-- statement:
--   Let $A$ be a real symmetric $n\times n$ matrix, $b\in\mathbb R^n$, and $f(x)=\tfrac12\langle x,Ax\rangle+\langle b,x\rangle$. If $\mu\in\mathbb R$ and $y\in\mathbb R^n$ satisfy $(A+\mu I)y=-b$, then for every $x\in\mathbb R^n$
--   $$f(x)=f(y)-\frac{\mu}{2}\bigl(\|x\|^2-\|y\|^2\bigr)+\frac12\bigl\langle x-y,(A+\mu I)(x-y)\bigr\rangle .$$
--
--   Applied at a Kuhn–Tucker point $y=x^*$ with $\mu=\lambda^*$ this is (22), the expansion from which every restart point of §4.2 is shown to decrease $f$.
-- source:
--   Pham Dinh & Le Thi, A d.c. optimization algorithm for solving the trust-region subproblem, SIAM J. Optim. 8 (1998), p. 492, Lemma 4.2

import Mathlib
import Definitions.Def_TaoAnDCA_Restart_Setting

namespace TaoAnDCA.Restart

theorem lemma_4_2 {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b : EuclideanSpace ℝ (Fin n)) (mu : ℝ) (y : EuclideanSpace ℝ (Fin n)) (hy : A y + mu • y = -b) :
    ∀ x : EuclideanSpace ℝ (Fin n), TaoAnDCA.TRS.quad A b x = TaoAnDCA.TRS.quad A b y - mu / 2 * (‖x‖ ^ 2 - ‖y‖ ^ 2)
      + 1 / 2 * inner ℝ (x - y) (A (x - y) + mu • (x - y)) := by sorry

end TaoAnDCA.Restart
