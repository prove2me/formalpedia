-- Prove2me | Theorems.Thm_RevenueManagement_overbooking_limit_policy
-- name    : RevenueManagement.overbooking_limit_policy
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:39:32.218946+00:00
-- url     : https://prove2.me/theorems/215d66c2-2448-40f5-9e96-f4439b88c0a9
-- title:
--   Proposition 4.1: with a convex denied-service cost, an overbooking-limit policy is optimal in the dynamic overbooking model
-- statement:
--   In the dynamic overbooking model with a convex denied-service cost $c$, in every period
--   $1 \le t \le T$ the overbooking-limit policy with the greatest optimal limit $x^*(t)$ is
--   optimal: with $y$ reservations on hand and $d$ new requests, booking
--   $\min\{y + d, \max\{y, x^*(t)\}\}$, that is accepting new reservations until the total on
--   hand reaches $x^*(t)$, attains the maximum of $v_{t+1}(x) + (x - y)\,p(t)$ over
--   $y \le x \le y + d$. When $x^*(t) = \infty$ the policy accepts every request.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, p. 153, Proposition 4.1 (the model is a simplification of Chatwin's, Sect. 4.3.1)

import Definitions.Def_RevenueManagement_overbooking

namespace RevenueManagement

theorem overbooking_limit_policy (M : DynOverbooking) (hM : M.IsModel) (hc : IsConvexSeq M.c)
    (t : ℕ) (ht : 1 ≤ t) (htT : t ≤ M.T) (y d : ℕ) :
    M.IsOptimalLevel t y d (limitPolicy (M.overbookingLimit t) y d) := by sorry

end RevenueManagement
