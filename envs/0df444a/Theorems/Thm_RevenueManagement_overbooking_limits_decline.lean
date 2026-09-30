-- Prove2me | Theorems.Thm_RevenueManagement_overbooking_limits_decline
-- name    : RevenueManagement.overbooking_limits_decline
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:40:00.105631+00:00
-- url     : https://prove2.me/theorems/80944bb5-19e6-4666-9d66-27a5701c2362
-- title:
--   Proposition 4.2: if qₜ(p(t) − p(t+1)) + (1 − qₜ)(p(t) − r(t)) ≥ 0, the greatest optimal overbooking limits decline with time, x*(1) ≥ x*(2) ≥ ··· ≥ x*(T)
-- statement:
--   In the dynamic overbooking model with a convex denied-service cost, if the survival
--   probabilities, revenues and refunds satisfy
--   $q_t\,(p(t) - p(t+1)) + (1 - q_t)\,(p(t) - r(t)) \ge 0$ for $1 \le t < T$, then the greatest
--   optimal overbooking limits decline with time: $x^*(t+1) \le x^*(t)$ for every
--   $1 \le t < T$, in $\mathbb N \cup \{\infty\}$. The condition holds in particular when
--   revenues decrease over time and refunds do not exceed the current price.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, p. 153, Proposition 4.2 and its footnote

import Definitions.Def_RevenueManagement_overbooking

namespace RevenueManagement

theorem overbooking_limits_decline (M : DynOverbooking) (hM : M.IsModel) (hc : IsConvexSeq M.c)
    (hcond : ∀ t, 1 ≤ t → t < M.T →
      0 ≤ M.q t * (M.p t - M.p (t + 1)) + (1 - M.q t) * (M.p t - M.r t))
    (t : ℕ) (ht : 1 ≤ t) (htT : t < M.T) :
    M.overbookingLimit (t + 1) ≤ M.overbookingLimit t := by sorry

end RevenueManagement
