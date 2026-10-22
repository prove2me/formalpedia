-- Prove2me | Theorems.Thm_ReferencePricing_PriceMonotone_lemma2_optRef_monotone
-- name    : ReferencePricing.PriceMonotone.lemma2_optRef_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T14:56:49.018752+00:00
-- url     : https://prove2.me/theorems/ed0faab2-8b8f-4b43-a3d7-ab0e7f08dcbc
-- title:
--   Lemma 2 — the optimal reference price policy q*(r) is increasing in r
-- statement:
--   **Lemma 2 (Monotone Reference Price Policy), Popescu and Wu 2007, p. 419.** Consider the dynamic pricing problem with reference effects: prices lie in $P = [0,\bar p]$ with $\bar p > 0$, and the reference price evolves as $r_{t+1} = \alpha r_t + (1-\alpha)p_t$ with memory $\alpha \in [0,1)$. Future profits are discounted by $\beta \in (0,1)$. Demand is $D(p,r) = d(p) + R(r-p,r)$, and the short-term profit is $\Pi(p,r) = p\,D(p,r)$. Let $V$ be the value function and $W(p,r) = \Pi(p,r) + \beta V(\alpha r + (1-\alpha)p)$. Let $p^*(r)$ be the largest maximizer of $W(\cdot, r)$ over $P$, and $q^*(r) = \alpha r + (1-\alpha)p^*(r)$. Assume Assumptions 1–3 and that the base demand $d$ is differentiable. Then the reference price policy is increasing on $P$:
--   $$r_1, r_2 \in P,\ r_1 \le r_2 \ \Longrightarrow\ q^*(r_1) \le q^*(r_2).$$
--
--   The next reference price produced by optimal pricing is monotone in the current one. This monotonicity is what drives the monotone convergence of the state paths in Theorem 2.
--
--   **Formalization Note.** "Increases" is read as non-strict (`MonotoneOn` on $P$). The paper does not assume that $d$ is differentiable; the hypothesis `Differentiable ℝ d` is added so that $\pi'$ in Assumption 3(b) is a true derivative. It is a standing hypothesis of every item of this mission.
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 419, Lemma 2 (proof: Appendix A.5, p. 426)

import Mathlib
import Definitions.Def_RobustBooking_Shared_Assumptions
import Definitions.Def_RobustBooking_Shared_optPrice
open RobustBooking.Shared

namespace ReferencePricing.PriceMonotone

theorem lemma2_optRef_monotone
    (pbar α β : ℝ) (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hA1 : Assumption1 pbar d R) (hA2 : Assumption2 R) (hA3 : Assumption3 pbar d R)
    (hd : Differentiable ℝ d) :
    MonotoneOn (optRef (profit d R) α β pbar) (Set.Icc (0 : ℝ) pbar) := by sorry

end ReferencePricing.PriceMonotone
