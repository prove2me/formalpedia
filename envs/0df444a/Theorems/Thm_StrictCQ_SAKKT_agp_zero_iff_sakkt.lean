-- Prove2me | Theorems.Thm_StrictCQ_SAKKT_agp_zero_iff_sakkt
-- name    : StrictCQ.SAKKT.agp_zero_iff_sakkt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:35:50.253652+00:00
-- url     : https://prove2.me/theorems/80996190-5e01-431d-a367-e9aa9a21d937
-- title:
--   AGP(0) ⟺ SAKKT, p. 6 ([22, Theorem 1.2.6(c)], used in the proof of Theorem 4.5, pp. 11–12)
-- statement:
--   Let the constraint functions be continuously differentiable, let $x^*$ be feasible, and let $f$ be a continuously differentiable objective. Then
--   $$x^* \text{ satisfies AGP}(0)\text{ for } f\iff x^*\text{ satisfies SAKKT for } f.$$
--   Here AGP(0) asks for $x^k\to x^*$ with $P_{\Omega(x^k,0)}(x^k-\nabla f(x^k))-x^k\to0$, and SAKKT asks for $x^k\to x^*$, $\lambda^k\in\mathbb R^m$, $\mu^k\in\mathbb R^p_+$ with $\mu^k_j=0$ whenever $g_j(x^k)<0$, such that $\nabla f(x^k)+\sum_i\lambda_i^k\nabla h_i(x^k)+\sum_j\mu_j^k\nabla g_j(x^k)\to0$.
--
--   The paper takes this equivalence from Haeser and Schuverdt (its reference [22]) and uses both directions in the proof of Theorem 4.5: SAKKT is turned into AGP(0) to reach the normal cones of $\Omega(x^k,0)$, and AGP(0) is turned back into SAKKT for the linear objective built from an element of the outer limit.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 6 (AGP(0) is equivalent to SAKKT [22]); p. 12, proof of Theorem 4.5 ([22, Theorem 1.2.6(c)])

import Mathlib
import Definitions.Def_StrictCQ_SAKKT_Conditions

open Filter Topology InnerProductSpace

namespace StrictCQ.SAKKT

/-- p. 6 ([22, Theorem 1.2.6(c)]): AGP(0) holds at `xs` for `f` iff SAKKT holds at `xs` for `f`. -/
theorem agp_zero_iff_sakkt {n m p : ℕ} (C : Constraints n m p) (hC : C.IsC1)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ C.feasible)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f) :
    C.AGP 0 f xs ↔ C.SAKKT f xs := by sorry

end StrictCQ.SAKKT
