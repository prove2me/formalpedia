-- Prove2me | Theorems.Thm_ServiceParts_BaseStock_L_convex
-- name    : ServiceParts.BaseStock.L_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T21:25:20.34892+00:00
-- url     : https://prove2.me/theorems/3b238a4d-5033-42c3-bdd8-3b6750fd1477
-- title:
--   Convexity of the one-period holding and backorder cost $L$
-- statement:
--   In the model of Section 2.1, the expected one-period holding and backorder cost
--   $$
--   L(y) = \begin{cases} h\displaystyle\int_0^y (y-x)\,g(x)\,dx + b\int_y^\infty (x-y)\,g(x)\,dx, & y > 0,\\[2mm] b\displaystyle\int_0^\infty (x-y)\,g(x)\,dx, & y \le 0, \end{cases}
--   $$
--   is a convex function of $y \in \mathbb R$.
--
--   Convexity of $L$ is the base on which convexity of every value function $f_n$, and hence the order-up-to form of the optimal policy, is built.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 21, Section 2.1 (proof of Theorem 2)

import Mathlib
import Definitions.Def_ServiceParts_BaseStock_Model

open MeasureTheory Set

namespace ServiceParts.BaseStock

/-- Section 2.1, p. 21: "Given our assumptions, L(y) is a convex function of y." -/
theorem L_convex (M : Model) : ConvexOn ℝ univ M.L := by sorry

end ServiceParts.BaseStock
