-- Prove2me | Theorems.Thm_SPHardness_OrderPolytope_expRecourse_eq
-- name    : SPHardness.OrderPolytope.expRecourse_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:10:17.950978+00:00
-- url     : https://prove2.me/theorems/e8c3831b-d694-4481-9fbe-cff5652fcc80
-- title:
--   Proof of Theorem 3, p. 11 — expected recourse equals one minus order-polytope volume
-- statement:
--   For a finite poset $P$, let $Q(P)$ be the expected optimal value of (10) under the uniform law on $[0,1]^P$, and let $V(P)$ be the volume of its order polytope. Then
--
--   $$
--   Q(P)=1-V(P).
--   $$
--
--   This converts an approximation of the expected recourse value into an approximation of order-polytope volume with the same absolute error.
--
--   **Formalization Note** The expectation is a Lebesgue integral over the unit cube, whose volume is one.
-- source:
--   Hanasusanto, Kuhn & Wiesemann, A comment on "computational complexity of stochastic programming problems", Optimization Online preprint 2015/03/4825 (version of October 6, 2015), p. 11, proof of Theorem 3, displayed identity. https://optimization-online.org/wp-content/uploads/2015/03/4825.pdf

import Mathlib
import Definitions.Def_SPHardness_OrderPolytope_Model

namespace SPHardness.OrderPolytope

/-- Expected recourse equals the volume of the complement of the order polytope. -/
theorem expRecourse_eq (P : Type) [Fintype P] [PartialOrder P] :
    expRecourse P = 1 - volOrder P := by sorry

end SPHardness.OrderPolytope
