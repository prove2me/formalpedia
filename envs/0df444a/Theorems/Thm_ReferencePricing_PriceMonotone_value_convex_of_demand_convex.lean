-- Prove2me | Theorems.Thm_ReferencePricing_PriceMonotone_value_convex_of_demand_convex
-- name    : ReferencePricing.PriceMonotone.value_convex_of_demand_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T14:57:26.063457+00:00
-- url     : https://prove2.me/theorems/803127d9-b9fa-4726-bc82-752e29ed625a
-- title:
--   §A.7(b) — if demand D(p, r) is convex in r, the value function V(r) is convex in r
-- statement:
--   **Convexity of the value function (Popescu and Wu 2007, Appendix A.7(b), p. 426).** In the dynamic pricing problem with reference effects (price set $P = [0,\bar p]$ with $\bar p > 0$, memory $\alpha \in [0,1)$, discount $\beta \in (0,1)$, demand $D(p,r) = d(p) + R(r-p,r)$, short-term profit $\Pi(p,r) = p\,D(p,r)$), assume Assumptions 1–3 and that $d$ is differentiable. Suppose that demand is convex in the reference price: for every $p \in P$, $r \mapsto D(p, r)$ is convex on $P$. Then the value function
--   $$V(r_0) = \sup_{p_t \in P} \sum_{t \ge 0} \beta^t\, \Pi(p_t, r_t), \qquad r_{t+1} = \alpha r_t + (1-\alpha) p_t,$$
--   is convex on $P$.
--
--   This is the step of the proof of Lemma 3(b) that makes the Bellman objective $W(p, r) = \Pi(p,r) + \beta V(\alpha r + (1-\alpha)p)$ supermodular. The paper attributes it to Smith and McCardle (2002, Proposition 5).
--
--   **Formalization Note.** Convexity is required on the price set $P$, the domain of the reference price. $V$ is the supremum over price sequences (see the definition `value`). `Differentiable ℝ d` is added, as in every item of the mission.
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 426, Appendix A.7(b), second sentence

import Mathlib
import Definitions.Def_RobustBooking_Shared_Assumptions
import Definitions.Def_RobustBooking_Shared_optPrice
open RobustBooking.Shared

namespace ReferencePricing.PriceMonotone

theorem value_convex_of_demand_convex
    (pbar α β : ℝ) (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hA1 : Assumption1 pbar d R) (hA2 : Assumption2 R) (hA3 : Assumption3 pbar d R)
    (hd : Differentiable ℝ d)
    (hconv : ∀ p ∈ Set.Icc (0 : ℝ) pbar,
      ConvexOn ℝ (Set.Icc (0 : ℝ) pbar) (fun r => demand d R p r)) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) pbar) (value (profit d R) α β pbar) := by sorry

end ReferencePricing.PriceMonotone
