-- Prove2me | Theorems.Thm_StrictCQ_SAKKT_eq_4_22_normalCone_eq_polar
-- name    : StrictCQ.SAKKT.eq_4_22_normalCone_eq_polar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:32:14.201925+00:00
-- url     : https://prove2.me/theorems/6ba8e461-7c59-4530-82ad-18fda667ff19
-- title:
--   (4.22), p. 10 — at a feasible x*, N_{Ω(x*,0)}(x*) = L_Ω(x*)°
-- statement:
--   Let $x^*$ be a feasible point of (1.1). Then the normal cone of the linearized set $\Omega(x^*,0)$ at $x^*$ is the polar of the linearized cone:
--   $$N_{\Omega(x^*,0)}(x^*)=L_\Omega(x^*)^\circ.$$
--
--   This is the identity at the end of (4.22) in Definition 4.3: it says that the outer semicontinuity required by SAKKT-regularity has the polar of the linearized cone as its target.
--
--   **Formalization Note** No differentiability is needed: only the gradient vectors at $x^*$ enter. Feasibility matters: at a feasible $x^*$ the rows of $\Omega(x^*,0)$ with $g_j(x^*)\ge0$ are exactly the active ones.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 10, (4.22)

import Mathlib
import Definitions.Def_StrictCQ_SAKKT_Setting

open Filter Topology InnerProductSpace

namespace StrictCQ.SAKKT

/-- (4.22), right-hand equality: at a feasible `xs`, `N_{Ω(xs,0)}(xs) = L_Ω(xs)°`. -/
theorem eq_4_22_normalCone_eq_polar {n m p : ℕ} (C : Constraints n m p)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ C.feasible) :
    StrictCQ.AGP.normalCone (C.linSet xs 0) xs = StrictCQ.AGP.polar (C.linCone xs) := by sorry

end StrictCQ.SAKKT
