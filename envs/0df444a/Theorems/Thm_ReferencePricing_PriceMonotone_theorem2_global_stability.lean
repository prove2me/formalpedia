-- Prove2me | Theorems.Thm_ReferencePricing_PriceMonotone_theorem2_global_stability
-- name    : ReferencePricing.PriceMonotone.theorem2_global_stability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T14:56:59.640049+00:00
-- url     : https://prove2.me/theorems/97990260-fc41-451d-bc03-8689d2f135c2
-- title:
--   Theorem 2 — a unique steady state p** solving (3); all price paths converge to it and all state paths converge to it monotonically
-- statement:
--   **Theorem 2 (Global Stability and State-Path Monotonicity), Popescu and Wu 2007, p. 419.** In the dynamic pricing problem with reference effects (price set $P = [0,\bar p]$ with $\bar p > 0$, memory $\alpha \in [0,1)$, discount $\beta \in (0,1)$, demand $D(p,r) = d(p) + R(r-p,r)$, short-term profit $\Pi(p,r) = p\,D(p,r)$), assume Assumptions 1–3 and that $d$ is differentiable. Let $p^*$ be the largest-maximizer pricing policy of the Bellman equation (2), $q^*(r) = \alpha r + (1-\alpha)p^*(r)$, and for $r_0 \in P$ let $(r^*_t)$ be the state path and $(p^*_t)$ the pricing path. Then there is a price $p^{**}$ such that:
--
--   1. $p^{**}$ is a steady state ($p^{**} \in P$ and $p^*(p^{**}) = p^{**}$), and it is the only steady state;
--   2. $p^{**}$ is characterized by Theorem 1: it solves
--   $$\frac{\pi'(p)}{1-\beta} = \frac{p\,\lambda(p)}{1-\alpha\beta}, \tag{3}$$
--   and it is the only solution of (3) in $P$;
--   3. for every initial reference price $r_0 \in P$, the pricing path $p^*_t$ converges to $p^{**}$, and the state path $r^*_t$ is monotone (nondecreasing or nonincreasing) and converges to $p^{**}$.
--
--   Here $\pi(p) = p\,d(p)$ and $\lambda(r) = R_x(0,r)$.
--
--   **Formalization Note.** "Characterized by Theorem 1" is rendered as the pair of clauses in item 2. "Monotonically" means the whole state path is monotone from $t = 0$. The paper does not assume that $d$ is differentiable; that hypothesis is added. This is also Theorem 2 of the companion mission on loss aversion. Draft items cannot import each other, so it is restated here in this mission's namespace.
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 419, Theorem 2 (proof: Appendix A.6, p. 426); Equation (3) from Theorem 1, p. 418

import Mathlib
import Definitions.Def_RobustBooking_Shared_Assumptions
import Definitions.Def_RobustBooking_Shared_optPrice
open RobustBooking.Shared

open Filter Topology

namespace ReferencePricing.PriceMonotone

theorem theorem2_global_stability
    (pbar α β : ℝ) (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hA1 : Assumption1 pbar d R) (hA2 : Assumption2 R) (hA3 : Assumption3 pbar d R)
    (hd : Differentiable ℝ d) :
    ∃ p : ℝ, IsSteadyState (profit d R) α β pbar p ∧
      (∀ q : ℝ, IsSteadyState (profit d R) α β pbar q → q = p) ∧
      deriv (baseProfit d) p / (1 - β) = p * refSlope R p / (1 - α * β) ∧
      (∀ q ∈ Set.Icc (0 : ℝ) pbar,
        deriv (baseProfit d) q / (1 - β) = q * refSlope R q / (1 - α * β) → q = p) ∧
      ∀ r₀ ∈ Set.Icc (0 : ℝ) pbar,
        Tendsto (pricePath (profit d R) α β pbar r₀) atTop (𝓝 p) ∧
        (Monotone (statePath (profit d R) α β pbar r₀) ∨
          Antitone (statePath (profit d R) α β pbar r₀)) ∧
        Tendsto (statePath (profit d R) α β pbar r₀) atTop (𝓝 p) := by sorry

end ReferencePricing.PriceMonotone
