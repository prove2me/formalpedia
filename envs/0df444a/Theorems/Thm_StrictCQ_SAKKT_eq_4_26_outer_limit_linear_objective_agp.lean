-- Prove2me | Theorems.Thm_StrictCQ_SAKKT_eq_4_26_outer_limit_linear_objective_agp
-- name    : StrictCQ.SAKKT.eq_4_26_outer_limit_linear_objective_agp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:32:41.829978+00:00
-- url     : https://prove2.me/theorems/47f33455-aaf9-427b-a66f-f1b1695ec263
-- title:
--   (4.26), proof of Theorem 4.5, p. 12 — every ω* in the outer limit of N_{Ω(x,0)}(x) makes AGP(0) hold for f(x) = −⟨ω*, x⟩
-- statement:
--   Let the constraint functions be continuously differentiable and let $x^*$ be feasible. If
--   $$\omega^*\in\limsup_{x\to x^*}N_{\Omega(x,0)}(x),$$
--   then AGP(0) holds at $x^*$ for the linear objective $f(x)=-\langle\omega^*,x\rangle$.
--
--   The paper's argument takes $x^k\to x^*$ and $\omega^k\to\omega^*$ with $\omega^k\in N_{\Omega(x^k,0)}(x^k)$ and bounds $\|P_{\Omega(x^k,0)}(x^k+\omega^*)-x^k\|\le\|\omega^*-\omega^k\|$ (4.26). This is the backward half of Theorem 4.5: it turns any element of the outer limit into an objective for which the sequential condition holds.
--
--   **Formalization Note** AGP(0) is stated with the projection as a predicate, so the conclusion asserts the existence of the projections $y^k$ with $y^k-x^k\to0$. The gradient of $f$ is $-\omega^*$ at every point.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 12, (4.26), proof of Theorem 4.5

import Mathlib
import Definitions.Def_StrictCQ_SAKKT_Conditions

open Filter Topology InnerProductSpace

namespace StrictCQ.SAKKT

/-- (4.26): every `w` in the outer limit of `x ↦ N_{Ω(x,0)}(x)` at `xs` makes AGP(0) hold at `xs`
for the linear objective `f(x) = -⟨w, x⟩`. -/
theorem eq_4_26_outer_limit_linear_objective_agp {n m p : ℕ} (C : Constraints n m p)
    (hC : C.IsC1) (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ C.feasible)
    (w : EuclideanSpace ℝ (Fin n))
    (hw : w ∈ StrictCQ.AGP.outerLimitWithin (fun x => StrictCQ.AGP.normalCone (C.linSet x 0) x) Set.univ xs) :
    C.AGP 0 (fun x => -⟪w, x⟫_ℝ) xs := by sorry

end StrictCQ.SAKKT
