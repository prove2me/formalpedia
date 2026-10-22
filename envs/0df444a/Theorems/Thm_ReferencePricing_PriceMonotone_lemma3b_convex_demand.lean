-- Prove2me | Theorems.Thm_ReferencePricing_PriceMonotone_lemma3b_convex_demand
-- name    : ReferencePricing.PriceMonotone.lemma3b_convex_demand
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T14:57:39.356187+00:00
-- url     : https://prove2.me/theorems/f36d0352-9020-440e-87b3-f510e7bd350d
-- title:
--   Lemma 3(b) — if demand D(p, r) is convex in r, the optimal pricing policy p*(r) is increasing in r
-- statement:
--   **Lemma 3(b) (Monotone Price Policy under convex demand), Popescu and Wu 2007, p. 420.** In the dynamic pricing problem with reference effects (price set $P = [0,\bar p]$ with $\bar p > 0$, memory $\alpha \in [0,1)$, discount $\beta \in (0,1)$, demand $D(p,r) = d(p) + R(r-p,r)$, short-term profit $\Pi(p,r) = p\,D(p,r)$), assume Assumptions 1–3 and that $d$ is differentiable. If demand $D(p, r)$, or equivalently the reference effect $R(r-p, r)$, is convex in $r$ on $P$ for every $p \in P$, then the optimal pricing policy is increasing on $P$:
--   $$r_1, r_2 \in P,\ r_1 \le r_2 \ \Longrightarrow\ p^*(r_1) \le p^*(r_2),$$
--   where $p^*(r)$ is the largest maximizer over $P$ of $W(p, r) = \Pi(p,r) + \beta V(\alpha r + (1-\alpha)p)$.
--
--   Linear demand models, such as the additive-difference model $R(x, r) = \lambda x$, satisfy this condition. For those models the paper recovers earlier price-monotonicity results.
--
--   **Formalization Note.** "Increasing" is non-strict (`MonotoneOn` on $P$). `Differentiable ℝ d` is added, as in every item of the mission.
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 420, Lemma 3(b) (proof: Appendix A.7(b), p. 426)

import Mathlib
import Definitions.Def_RobustBooking_Shared_Assumptions
import Definitions.Def_RobustBooking_Shared_optPrice
open RobustBooking.Shared

namespace ReferencePricing.PriceMonotone

theorem lemma3b_convex_demand
    (pbar α β : ℝ) (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hA1 : Assumption1 pbar d R) (hA2 : Assumption2 R) (hA3 : Assumption3 pbar d R)
    (hd : Differentiable ℝ d)
    (hconv : ∀ p ∈ Set.Icc (0 : ℝ) pbar,
      ConvexOn ℝ (Set.Icc (0 : ℝ) pbar) (fun r => demand d R p r)) :
    MonotoneOn (optPrice (profit d R) α β pbar) (Set.Icc (0 : ℝ) pbar) := by sorry

end ReferencePricing.PriceMonotone
