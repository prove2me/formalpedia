-- Prove2me | Theorems.Thm_ReferencePricing_PriceMonotone_theorem3_global_price_monotonicity
-- name    : ReferencePricing.PriceMonotone.theorem3_global_price_monotonicity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T15:08:53.472038+00:00
-- url     : https://prove2.me/theorems/d1154cf3-e9c6-42d7-9433-6c025f01ecb9
-- title:
--   Theorem 3 (Global Price Monotonicity) — under any condition of Lemma 3, every optimal pricing path converges monotonically to the unique steady state p**
-- statement:
--   **Theorem 3 (Global Price Monotonicity), Popescu and Wu 2007, p. 420.** Consider the dynamic pricing problem with reference effects. Prices lie in $P = [0,\bar p]$ with $\bar p > 0$. The reference price evolves as $r_{t+1} = \alpha r_t + (1-\alpha)p_t$ with memory $\alpha \in [0,1)$, and profits are discounted by $\beta \in (0,1)$. Demand is $D(p,r) = d(p) + R(r-p,r)$ and the short-term profit is $\Pi(p,r) = p\,D(p,r)$. Let $V$ be the value function, $p^*(r)$ the largest maximizer over $P$ of $W(p,r) = \Pi(p,r) + \beta V(\alpha r + (1-\alpha)p)$, and $q^*(r) = \alpha r + (1-\alpha)p^*(r)$. For $r_0 \in P$ the state path is $r^*_0 = r_0$, $r^*_{t+1} = q^*(r^*_t)$, and the optimal pricing path is $p^*_t = p^*(r^*_t)$.
--
--   Assume Assumptions 1–3 and that $d$ is differentiable. Assume also that **at least one** of the alternative conditions of Lemma 3 holds:
--   (a) $\alpha = 0$;
--   (b) $D(p, r)$ is convex in $r$ on $P$ for every $p \in P$;
--   (c) $\Pi$ is strongly concave on $(0,\bar p)^2$ and, for one constant $K > 0$, $\Pi_{rr} \ge -K$ and $\Pi_{pr} \ge K/2$ there.
--
--   Then there is a price $p^{**}$ with the following properties. It is the unique steady state of the problem. It is the unique solution in $P$ of
--   $$\frac{\pi'(p)}{1-\beta} = \frac{p\,\lambda(p)}{1-\alpha\beta}, \tag{3}$$
--   where $\pi(p) = p\,d(p)$ and $\lambda(r) = R_x(0,r)$. And for every initial reference price $r_0 \in P$, the optimal pricing path $(p^*_t)_{t \ge 0}$ is monotone (nondecreasing or nonincreasing) and converges to $p^{**}$.
--
--   Consequently only three pricing strategies can be optimal: skimming (prices decreasing), penetration (prices increasing), and constant pricing.
--
--   **Formalization Note.** The hypothesis is the disjunction `LemmaThreeCondition`, as the paper's "alternative conditions" require. "Monotonically" means the whole pricing path is monotone from $t = 0$, not only eventually. "The unique steady-state price $p^{**}$, characterized by Theorem 1" is rendered as existence and uniqueness of the steady state, together with $p^{**}$ being the unique solution of (3) in $P$. `Differentiable ℝ d` is added because the paper writes $\pi'$ without assuming it exists.
--
--   Condition (c) is kept exactly as printed, although on $P = [0, \bar p]$ it can rarely hold. Strong concavity forces $\Pi_{rr} \le -2b < 0$ on the whole open square. But $\Pi_{rr} = p\,D_{rr}$, which tends to $0$ as $p \to 0$ whenever $D_{rr}$ stays bounded. The paper's own use of (c) (linear relative-difference models) is on a price range with a positive lower bound. A near-vacuous disjunct only weakens the hypothesis, so it does not trivialize the theorem, whose content comes from (a) and (b). The hypotheses are jointly satisfiable: $\bar p = 3/4$, $d(p) = 1-p$, $R(x, r) = x/4$ satisfies Assumptions 1–3 and condition (b) for every $\alpha \in [0,1)$ and $\beta \in (0,1)$.
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 420, Theorem 3 (proof: Lemma 3 with Theorem 2; Appendix A.6–A.7, pp. 426–427)

import Mathlib
import Definitions.Def_RobustBooking_Shared_Assumptions
import Definitions.Def_RobustBooking_Shared_optPrice
import Definitions.Def_ReferencePricing_PriceMonotone_LemmaThreeCondition
open RobustBooking.Shared

open Filter Topology

namespace ReferencePricing.PriceMonotone

theorem theorem3_global_price_monotonicity
    (pbar α β : ℝ) (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hA1 : Assumption1 pbar d R) (hA2 : Assumption2 R) (hA3 : Assumption3 pbar d R)
    (hd : Differentiable ℝ d)
    (hL3 : LemmaThreeCondition pbar α d R) :
    ∃ p : ℝ, IsSteadyState (profit d R) α β pbar p ∧
      (∀ q : ℝ, IsSteadyState (profit d R) α β pbar q → q = p) ∧
      deriv (baseProfit d) p / (1 - β) = p * refSlope R p / (1 - α * β) ∧
      (∀ q ∈ Set.Icc (0 : ℝ) pbar,
        deriv (baseProfit d) q / (1 - β) = q * refSlope R q / (1 - α * β) → q = p) ∧
      ∀ r₀ ∈ Set.Icc (0 : ℝ) pbar,
        (Monotone (pricePath (profit d R) α β pbar r₀) ∨
          Antitone (pricePath (profit d R) α β pbar r₀)) ∧
        Tendsto (pricePath (profit d R) α β pbar r₀) atTop (𝓝 p) := by sorry

end ReferencePricing.PriceMonotone
