-- Prove2me | Theorems.Thm_TaoAnDCA_TRS_dcaStep_spec
-- name    : TaoAnDCA.TRS.dcaStep_spec
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:23:57.043197+00:00
-- url     : https://prove2.me/theorems/88cb00b9-5889-40c9-bb7f-b946f5bb901a
-- title:
--   §4.1, (18)–(19), p. 490 — the DCA box step is the projection P_E(x − (Ax + b)/ρ) and a simplified-DCA step for (16)
-- statement:
--   Let $A$ be a real symmetric $n\times n$ matrix, $b\in\mathbb R^n$, $r>0$, $E = \{x:\|x\|\le r\}$, and let $\rho>0$ be such that $\rho I - A$ is positive semidefinite. Let $g, h$ be the decomposition (16) of the trust-region objective, $g(x) = \frac12\rho\|x\|^2 + b^Tx + \chi_E(x)$ and $h(x) = \frac12x^T(\rho I-A)x$. Fix $x^k\in\mathbb R^n$, put $y^k = (\rho I - A)x^k$, and let $x^{k+1}$ be given by the DCA box: $x^{k+1} = w/\rho$ if $\|w\|\le\rho r$, and $x^{k+1} = r\,w/\|w\|$ otherwise, where $w = y^k - b$. Then:
--   1. $\|x^{k+1}\|\le r$;
--   2. $x^{k+1}$ solves (18):
--   $$\min\Big\{\tfrac{\rho}{2}\|x\|^2 + x^T(b - y^k) + \chi_E(x) : x\in\mathbb R^n\Big\};$$
--   3. $x^{k+1}$ is the Euclidean projection (19)
--   $$x^{k+1} = P_E\Big(x^k - \tfrac1\rho(Ax^k + b)\Big),$$
--   i.e. $\|x^{k+1} - (x^k - \frac1\rho(Ax^k+b))\|\le\|z - (x^k - \frac1\rho(Ax^k+b))\|$ for every $z\in E$;
--   4. $y^k\in\partial h(x^k)$ and $x^{k+1}\in\partial g^*(y^k)$.
--
--   Item 4 says that the explicit DCA box is the simplified DCA applied to the decomposition (16); this is what lets the general convergence theory of the DCA be applied to it.
--
--   **Formalization Note.** $A$ is a self-adjoint continuous linear operator on `EuclideanSpace ℝ (Fin n)`, and "$\rho I - A$ positive semidefinite" is $\langle z, \rho z - Az\rangle\ge 0$ for all $z$. The projection is stated by its defining minimality property.
-- source:
--   Pham Dinh & Le Thi, A d.c. optimization algorithm for solving the trust-region subproblem, SIAM J. Optim. 8 (1998), p. 490, §4.1, (16), (18), (19) and the DCA box

import Mathlib
import Definitions.Def_TaoAnDCA_TRS_Setting

open Filter Topology

namespace TaoAnDCA.TRS

theorem dcaStep_spec {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r) (ρ : ℝ) (hρ : 0 < ρ)
    (hρA : ∀ z : EuclideanSpace ℝ (Fin n), 0 ≤ inner ℝ z (ρ • z - A z)) (xk : EuclideanSpace ℝ (Fin n)) :
    ‖dcaStep A b ρ r xk‖ ≤ r ∧
    (∀ z : EuclideanSpace ℝ (Fin n), ‖z‖ ≤ r →
      ρ / 2 * ‖dcaStep A b ρ r xk‖ ^ 2 + inner ℝ (dcaStep A b ρ r xk) (b - (ρ • xk - A xk)) ≤
        ρ / 2 * ‖z‖ ^ 2 + inner ℝ z (b - (ρ • xk - A xk))) ∧
    (∀ z : EuclideanSpace ℝ (Fin n), ‖z‖ ≤ r →
      ‖dcaStep A b ρ r xk - (xk - (1 / ρ) • (A xk + b))‖ ≤ ‖z - (xk - (1 / ρ) • (A xk + b))‖) ∧
    (ρ • xk - A xk ∈ TaoAnDCA.GlobalOpt.subdiff (hDec A ρ) xk ∧
      dcaStep A b ρ r xk ∈ TaoAnDCA.GlobalOpt.subdiff (CondatPD.FinDim.conj (gDec b ρ r)) (ρ • xk - A xk)) := by sorry

end TaoAnDCA.TRS
