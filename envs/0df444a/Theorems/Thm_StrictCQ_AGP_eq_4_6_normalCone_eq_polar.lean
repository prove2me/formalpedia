-- Prove2me | Theorems.Thm_StrictCQ_AGP_eq_4_6_normalCone_eq_polar
-- name    : StrictCQ.AGP.eq_4_6_normalCone_eq_polar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:38:08.851161+00:00
-- url     : https://prove2.me/theorems/d32d8a1f-3783-4562-9158-9a262492cf08
-- title:
--   (4.6), p. 6 — at a feasible x*, N_{Ω(x*,−∞)}(x*) = L_Ω(x*)°
-- statement:
--   Let $x^*$ be a feasible point of (1.1). Then the normal cone at $x^*$ of the linearized set $\Omega(x^*,-\infty)$ of (4.2) is the polar of the linearized cone (3.7):
--
--   $$
--   N_{\Omega(x^*,-\infty)}(x^*)=L_\Omega(x^*)^\circ.
--   $$
--
--   This is the right-hand equality of (4.6); it identifies the target set of AGP-regularity with the cone of KKT gradients.
--
--   **Formalization Note** No differentiability is needed: only the gradient vectors at $x^*$ enter both sides.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 6, (4.6)

import Mathlib
import Definitions.Def_StrictCQ_AGP_Setting

open Filter Topology InnerProductSpace

namespace StrictCQ.AGP

/-- (4.6), right-hand equality: at a feasible `xs`, `N_{Ω(xs,-∞)}(xs) = L_Ω(xs)°`. -/
theorem eq_4_6_normalCone_eq_polar {n m p : ℕ} (C : Constraints n m p)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ C.feasible) :
    normalCone (C.linSet xs ⊥) xs = polar (C.linCone xs) := by sorry

end StrictCQ.AGP
