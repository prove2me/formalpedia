-- Prove2me | Theorems.Thm_StrictCQ_AGP_outer_limit_linear_objective_agp
-- name    : StrictCQ.AGP.outer_limit_linear_objective_agp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:39:43.118161+00:00
-- url     : https://prove2.me/theorems/5d910f36-6518-4094-b9b0-3f3c815166ce
-- title:
--   (4.10)–(4.11), proof of Theorem 4.2, p. 8 — every ω* in the outer limit makes AGP(−∞) hold for f(x) = −⟨ω*, x⟩
-- statement:
--   Let the constraint functions of (1.1) be $\mathrm C^1$ and $x^*$ feasible. If
--
--   $$
--   \omega^*\in\limsup_{(x,\varepsilon)\to(x^*,0)}N_{\Omega(x,-\infty)}(x+\varepsilon),
--   $$
--
--   then AGP($-\infty$) holds at $x^*$ for the linear objective $f(x)=-\langle\omega^*,x\rangle$.
--
--   This is the construction behind the second half of Theorem 4.2: any vector in the outer limit is the negative gradient of an objective for which AGP holds, so a constraint qualification that makes AGP imply KKT must place it in the polar of the linearized cone.
--
--   **Formalization Note** The paper writes both $\omega^*$ and $w^*$ for this vector; the formal statement uses one name. The outer limit is the sequential one of (1.6), over all $(x,\varepsilon)$.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 8, (4.10)–(4.11), proof of Theorem 4.2

import Mathlib
import Definitions.Def_StrictCQ_AGP_Conditions

open Filter Topology InnerProductSpace

namespace StrictCQ.AGP

/-- (4.10)–(4.11): every `w` in the outer limit of `N_{Ω(x,-∞)}(x + ε)` at `(xs, 0)` makes
AGP(-∞) hold at `xs` for the linear objective `f(x) = -⟨w, x⟩`. -/
theorem outer_limit_linear_objective_agp {n m p : ℕ} (C : Constraints n m p) (hC : C.IsC1)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ C.feasible) (w : EuclideanSpace ℝ (Fin n))
    (hw : w ∈ outerLimitWithin
      (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        normalCone (C.linSet q.1 ⊥) (q.1 + q.2))
      Set.univ (xs, 0)) :
    C.AGP ⊥ (fun x => -⟪w, x⟫_ℝ) xs := by sorry

end StrictCQ.AGP
