-- Prove2me | Theorems.Thm_ReferencePricing_PriceMonotone_lemma3a_short_memory
-- name    : ReferencePricing.PriceMonotone.lemma3a_short_memory
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T14:57:11.405373+00:00
-- url     : https://prove2.me/theorems/e70fb1f6-da97-435a-818f-aed7aea90c21
-- title:
--   Lemma 3(a) — with short memory α = 0 the optimal pricing policy p*(r) is increasing in r
-- statement:
--   **Lemma 3(a) (Monotone Price Policy under short memory), Popescu and Wu 2007, p. 420.** In the dynamic pricing problem with reference effects (price set $P = [0,\bar p]$ with $\bar p > 0$, discount $\beta \in (0,1)$, demand $D(p,r) = d(p) + R(r-p,r)$, short-term profit $\Pi(p,r) = p\,D(p,r)$), assume Assumptions 1–3 and that $d$ is differentiable. If consumers have short memory, $\alpha = 0$, so that the reference price equals the last price ($r_{t+1} = p_t$), then the optimal pricing policy is increasing on $P$:
--   $$r_1, r_2 \in P,\ r_1 \le r_2 \ \Longrightarrow\ p^*(r_1) \le p^*(r_2),$$
--   where $p^*(r)$ is the largest maximizer over $P$ of $W(p, r) = \Pi(p, r) + \beta V(p)$.
--
--   With $\alpha = 0$ the Bellman objective separates into the short-term profit and a term that depends on the price alone.
--
--   **Formalization Note.** The standing hypotheses $0 \le \alpha < 1$ remain as binders, together with the special case `α = 0`. "Increasing" is non-strict (`MonotoneOn` on $P$). `Differentiable ℝ d` is added, as in every item of the mission.
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 420, Lemma 3(a) (proof: Appendix A.7(a), p. 426)

import Mathlib
import Definitions.Def_RobustBooking_Shared_Assumptions
import Definitions.Def_RobustBooking_Shared_optPrice
open RobustBooking.Shared

namespace ReferencePricing.PriceMonotone

theorem lemma3a_short_memory
    (pbar α β : ℝ) (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hA1 : Assumption1 pbar d R) (hA2 : Assumption2 R) (hA3 : Assumption3 pbar d R)
    (hd : Differentiable ℝ d)
    (hα : α = 0) :
    MonotoneOn (optPrice (profit d R) α β pbar) (Set.Icc (0 : ℝ) pbar) := by sorry

end ReferencePricing.PriceMonotone
