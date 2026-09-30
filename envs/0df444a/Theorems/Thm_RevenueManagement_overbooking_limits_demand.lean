-- Prove2me | Theorems.Thm_RevenueManagement_overbooking_limits_demand
-- name    : RevenueManagement.overbooking_limits_demand
-- status  : Disproved
-- author  : @naimengye
-- created : 2026-09-24T00:40:48.739475+00:00
-- url     : https://prove2.me/theorems/4aef2e8e-a2ab-4201-b4c8-6d438b2fa257
-- title:
--   Proposition 4.3: with a convex denied-service cost, stochastically larger demand to come gives greatest optimal overbooking limits that are no larger
-- statement:
--   In the dynamic overbooking model with a convex denied-service cost, let $f'$ be a second
--   family of demand pmfs with $D'_t$ stochastically larger than $D_t$ in every period, that is
--   $\mathbb P(D_t \ge k) \le \mathbb P(D'_t \ge k)$ for all $t$ and $k$. Then the greatest
--   optimal overbooking limit of the model with demands $D'$ is at most that of the model with
--   demands $D$, in every period $1 \le t \le T$. This is the book's statement with the
--   parametrized family $D_t(\theta)$, stochastically increasing in $\theta$, replaced by two of
--   its members.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, pp. 153-154, Proposition 4.3 ('as demand to come increases (stochastically), it is better to be less aggressive in overbooking')

import Definitions.Def_RevenueManagement_overbooking

namespace RevenueManagement

theorem overbooking_limits_demand (M : DynOverbooking) (hM : M.IsModel) (hc : IsConvexSeq M.c)
    (f' : ℕ → ℕ → ℝ) (hf' : ∀ t, (∀ d, 0 ≤ f' t d) ∧ HasSum (f' t) 1)
    (hst : ∀ t k, ∑' d, (if k ≤ d then M.f t d else 0) ≤ ∑' d, (if k ≤ d then f' t d else 0))
    (t : ℕ) (ht : 1 ≤ t) (htT : t ≤ M.T) :
    ({ M with f := f' } : DynOverbooking).overbookingLimit t ≤ M.overbookingLimit t := by sorry

end RevenueManagement
