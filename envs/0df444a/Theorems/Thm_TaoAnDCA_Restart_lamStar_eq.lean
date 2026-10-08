-- Prove2me | Theorems.Thm_TaoAnDCA_Restart_lamStar_eq
-- name    : TaoAnDCA.Restart.lamStar_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:58:27.151955+00:00
-- url     : https://prove2.me/theorems/65221aa0-fc01-469a-ac4b-b2d3a1adbd0c
-- title:
--   §4.2, p. 491 — the multiplier of a Kuhn–Tucker point is λ* = (−⟨x*, Ax*⟩ − ⟨x*, b⟩)/r²
-- statement:
--   Let $A$ be a real symmetric $n\times n$ matrix, $b\in\mathbb R^n$, $r>0$, and let $x^*$ be a Kuhn–Tucker point of the trust-region subproblem $\min\{\tfrac12\langle x,Ax\rangle+\langle b,x\rangle:\|x\|\le r\}$ with multiplier $\lambda^*$, that is, $\lambda^*\ge0$, $(A+\lambda^*I)x^*=-b$, $\lambda^*(\|x^*\|-r)=0$ and $\|x^*\|\le r$. Then
--   $$\lambda^*=\frac{-\langle x^*,Ax^*\rangle-\langle x^*,b\rangle}{r^2}.$$
--
--   The multiplier is therefore computable from $x^*$ alone, which is what the global-optimality test of §4.2 ($\lambda^*+\lambda_1\ge 0$) needs.
--
--   **Formalization Note** The paper derives the formula "from Theorem 2.1"; the statement only uses the Kuhn–Tucker conditions. When $\|x^*\|<r$, complementarity gives $\lambda^*=0$ and the right-hand side vanishes as well, since $Ax^*=-b$.
-- source:
--   Pham Dinh & Le Thi, A d.c. optimization algorithm for solving the trust-region subproblem, SIAM J. Optim. 8 (1998), p. 491, §4.2, display after "from Theorem 2.1 it follows that"

import Mathlib
import Definitions.Def_TaoAnDCA_Restart_Setting

namespace TaoAnDCA.Restart

theorem lamStar_eq {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r)
    (xs : EuclideanSpace ℝ (Fin n)) (lamStar : ℝ) (hkkt : TaoAnDCA.TRS.IsKKT A b r xs lamStar) :
    lamStar = (-(inner ℝ xs (A xs)) - inner ℝ xs b) / r ^ 2 := by sorry

end TaoAnDCA.Restart
