-- Prove2me | Theorems.Thm_TaoAnDCA_TRS_eq20_iff_kkt
-- name    : TaoAnDCA.TRS.eq20_iff_kkt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:24:25.384168+00:00
-- url     : https://prove2.me/theorems/708bbd2b-a264-412b-a754-85117aca7861
-- title:
--   §4.1, (20), p. 491 — ∂h(x*) = {(ρI − A)x*} ⊂ ∂g(x*) iff x* is a Kuhn–Tucker point of (Q1)
-- statement:
--   Let $A$, $b$, $r>0$, $\rho>0$ and the decomposition (16) $g(x)=\frac12\rho\|x\|^2+b^Tx+\chi_E(x)$, $h(x)=\frac12x^T(\rho I-A)x$ be as in the trust-region setting, with $A$ symmetric and $\rho I-A$ positive semidefinite, and let $x^*\in E$, i.e. $\|x^*\|\le r$. Then $\partial h(x^*) = \{\nabla h(x^*)\} = \{(\rho I-A)x^*\}$, and the inclusion (20)
--   $$\partial h(x^*) = \nabla h(x^*)\subset\partial g(x^*)$$
--   holds if and only if there is a real $\lambda^*\ge0$ with
--   $$(A+\lambda^*I)x^* = -b,\qquad\lambda^*(\|x^*\|-r) = 0,\qquad\|x^*\|\le r.$$
--
--   This identifies the critical points that the DCA delivers for the decomposition (16) with the Kuhn–Tucker points of the trust-region subproblem.
--
--   **Formalization Note.** The Kuhn–Tucker conditions are the predicate `IsKKT A b r x lam`. The hypothesis $\|x^*\|\le r$ is where the page applies the equivalence: the limit points of the DCA lie in $E$.
-- source:
--   Pham Dinh & Le Thi, A d.c. optimization algorithm for solving the trust-region subproblem, SIAM J. Optim. 8 (1998), p. 491, §4.1, proof of Theorem 4.1, display (20) and the sentence after it

import Mathlib
import Definitions.Def_TaoAnDCA_TRS_Setting

open Filter Topology

namespace TaoAnDCA.TRS

theorem eq20_iff_kkt {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r) (ρ : ℝ) (hρ : 0 < ρ)
    (hρA : ∀ z : EuclideanSpace ℝ (Fin n), 0 ≤ inner ℝ z (ρ • z - A z)) (xs : EuclideanSpace ℝ (Fin n)) (hxs : ‖xs‖ ≤ r) :
    TaoAnDCA.GlobalOpt.subdiff (hDec A ρ) xs = {ρ • xs - A xs} ∧
      (TaoAnDCA.GlobalOpt.subdiff (hDec A ρ) xs ⊆ TaoAnDCA.GlobalOpt.subdiff (gDec b ρ r) xs ↔ ∃ lam : ℝ, IsKKT A b r xs lam) := by sorry

end TaoAnDCA.TRS
