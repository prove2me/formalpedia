-- Prove2me | Theorems.Thm_RevenueManagement_overbooking_limits_demand_v2
-- name    : RevenueManagement.overbooking_limits_demand_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:41:49.164974+00:00
-- url     : https://prove2.me/theorems/07c89f9b-45b2-4ddb-b8ad-67e97056a9a0
-- title:
--   Proposition 4.3: with a convex denied-service cost and finite-mean demands, stochastically larger demand to come gives greatest optimal overbooking limits that are no larger
-- statement:
--   In the dynamic overbooking model of §4.3.1 with a convex denied-service cost, let $f'$ be a second family of demand pmfs with $D'_t$ stochastically larger than $D_t$ in every period, that is $\mathbb P(D_t\ge k)\le\mathbb P(D'_t\ge k)$ for all $t$ and $k$, and assume that all demands have finite means. Then the greatest optimal overbooking limit of the model with demands $D'$ is at most that of the model with demands $D$, in every period $1\le t\le T$:
--   $$x'^*(t)\le x^*(t).$$
--   This is the book's Proposition 4.3 ("as demand to come increases stochastically, it is better to be less aggressive in overbooking") with the parametrized family $D_t(\theta)$, stochastically increasing in $\theta$, replaced by two of its members.
--
--   **Formalization Note.** The retired version had no moment hypothesis on the demands; the value recursion `valueGo` writes the expectation over $D_t$ as a `tsum`, which is $0$ for a non-summable family, so a heavy-tailed $f'$ with infinite mean collapsed $V'$ to $0$ and reversed the comparison (accepted disproof). The new statement adds the model's implicit assumption that every $D_t$ and $D'_t$ has a finite mean, $\sum_d d\,f_t(d)<\infty$ and $\sum_d d\,f'_t(d)<\infty$; under it every expectation in the recursion is a genuine (absolutely convergent) sum, because the inner maximum grows at most linearly in the demand. Everything else is as before: `IsModel` (pmfs, $0\le q_t\le1$, $p_t,r_t\ge0$, $c(0)=0$, $c\ge0$), convexity of $c$, the stochastic order through tail sums, and the greatest optimal limit as the `ℕ∞`-valued supremum of the levels that are at least as good as every smaller level (the greatest maximizer when the objective is concave).
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, pp. 153–154, Proposition 4.3, in the dynamic overbooking model of Sect. 4.3.1 (pp. 152–153), whose expectations are finite

import Definitions.Def_RevenueManagement_overbooking

namespace RevenueManagement

/-- Talluri & van Ryzin, *The Theory and Practice of Revenue Management*, pp. 153–154,
Proposition 4.3: in the dynamic overbooking model of §4.3.1 with a convex denied-service cost,
if the demand to come is stochastically larger (`D'_t ≥_st D_t` in every period), the greatest
optimal overbooking limit is no larger: `x'*(t) ≤ x*(t)` for `1 ≤ t ≤ T`.

Corrected version: the demands have **finite means**, `∑_d d f_t(d) < ∞` and
`∑_d d f'_t(d) < ∞` (the model's expectations, in particular the recursion for `V_t`, are
finite). The retired statement had no such hypothesis, and the `tsum` in `valueGo` returns `0`
for a demand law with infinite mean, so a heavy-tailed `f'` collapsed `V'` to `0` and reversed
the comparison. -/
theorem overbooking_limits_demand_v2 (M : DynOverbooking) (hM : M.IsModel)
    (hmean : ∀ t, Summable (fun d : ℕ => (d : ℝ) * M.f t d)) (hc : IsConvexSeq M.c)
    (f' : ℕ → ℕ → ℝ) (hf' : ∀ t, (∀ d, 0 ≤ f' t d) ∧ HasSum (f' t) 1)
    (hmean' : ∀ t, Summable (fun d : ℕ => (d : ℝ) * f' t d))
    (hst : ∀ t k, ∑' d, (if k ≤ d then M.f t d else 0) ≤ ∑' d, (if k ≤ d then f' t d else 0))
    (t : ℕ) (ht : 1 ≤ t) (htT : t ≤ M.T) :
    ({ M with f := f' } : DynOverbooking).overbookingLimit t ≤ M.overbookingLimit t := by sorry

end RevenueManagement
