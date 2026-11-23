-- Prove2me | Theorems.Thm_StrictCQ_Scaled_Supplement_lemma_6_3
-- name    : StrictCQ.Scaled.Supplement.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:57:22.981662+00:00
-- url     : https://prove2.me/theorems/49d1d89f-726a-49b4-8900-5af2e64ec41b
-- title:
--   Lemma 6.3 (corrected: normal vectors belong to ℝⁿ)
-- statement:
--   Let $C=(h,g)$ have continuously differentiable components on $\mathbb R^n$, let $\bar x\in\Omega$ be feasible, and let $y\in T_\Omega(\bar x)^\circ$, the polar of the Bouligand tangent cone. Let $\Omega_L$ be the feasible set of the affine constraints and $\Omega_{NL}(x,-\infty)$ the set in (4.27) obtained from the remaining constraints. There are sequences $x^k,\omega^k\in\mathbb R^n$ such that
--   $$x^k\in\Omega_L,\qquad x^k\to\bar x,\qquad\omega^k\to y,\qquad
--   \omega^k\in N_{\Omega_{NL}(x^k,-\infty)\cap\Omega_L}(x^k)\quad\text{for every }k.$$
--   This approximation statement supports the limiting-normal inclusion used in Theorem 6.5. No regularity qualification is assumed.
--
--   **Formalization Note** Normal cones are the imported convex normal cones, empty outside their sets. The statement uses sequences whose every term has the stated membership; discarding a finite initial segment of the proof's sequences gives this formulation.
--
--   Differences from the source:
--   - reading: C¹ constraints and a feasible base point supplied by the setting and Lemma 6.1 → explicit C.IsC1 and xb ∈ C.feasible; reason: the tangent cone is introduced at a point of the set on p. 4 and the proof invokes Lemma 6.1 at a feasible point
--   - correction: normal vectors ωᵏ ∈ ℝᵐ → normal vectors ωᵏ ∈ ℝⁿ; reason: the vectors are gradients of scalar functions on ℝⁿ and normals to subsets of ℝⁿ; the proof on p. 23 fixes their dimension
--   - encoding: linear constraints → affine constraints via the published IsAffine predicate; reason: this preserves the published LAGP model and the meaning of linear equalities and inequalities with constant terms
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 23, Lemma 6.3; pp. 4, 22 for feasibility context

import Mathlib
import Definitions.Def_StrictCQ_AGP_LAGP
import Definitions.Def_StrictCQ_CAKKT_Setting

open Filter Topology

namespace StrictCQ.Scaled.Supplement

/-- Lemma 6.3, p. 23: normals live in ℝⁿ, correcting the printed ℝᵐ. -/
theorem lemma_6_3 {n m p : ℕ} (C : StrictCQ.AGP.Constraints n m p)
    (xb y : EuclideanSpace ℝ (Fin n)) (hC : C.IsC1) (hxb : xb ∈ C.feasible)
    (hy : y ∈ StrictCQ.AGP.polar (StrictCQ.CAKKT.tangentCone C.feasible xb)) :
    ∃ x omega : ℕ → EuclideanSpace ℝ (Fin n),
      (∀ k, x k ∈ C.linPart) ∧ Tendsto x atTop (𝓝 xb) ∧
      Tendsto omega atTop (𝓝 y) ∧
      ∀ k, omega k ∈ StrictCQ.AGP.normalCone (C.nonlinSet (x k) ∩ C.linPart) (x k) := by sorry

end StrictCQ.Scaled.Supplement
