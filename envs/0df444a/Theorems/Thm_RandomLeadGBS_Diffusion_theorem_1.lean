-- Prove2me | Theorems.Thm_RandomLeadGBS_Diffusion_theorem_1
-- name    : RandomLeadGBS.Diffusion.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:15.941172+00:00
-- url     : https://prove2.me/theorems/17c0b2ec-b79c-446d-9cc0-3b2d73d9d2e3
-- title:
--   Theorem 1, pp. 10–11 — under GBS with integer γ ≥ 1 and exponential lead times, (Y^r(∞) − x∗)/√r ⇒ N(0, (βγ)^−1) and E[·]^± → (2πβγ)^−1/2
-- statement:
--   Consider a sequence of inventory systems indexed by the demand rate $r$: Poisson demand of rate $r$, i.i.d. exponential lead times with mean $1/\beta>0$, managed by the generalized base-stock policy with a fixed integer gain $\gamma\ge 1$, truncation $f(r)>0$ with $f(r)/r\to 0$ and $f(r)/\sqrt r\to\infty$, and an arbitrary centering $x_*(r)$. Let $(Y^r,Z^r)$ be the resulting chain of net inventory level and in-transit inventory. Then:
--
--   1. for every $r>0$ some state is reachable from every state (a single closed communicating class);
--   2. for every sufficiently large $r$ the chain has a unique stationary distribution;
--   3. for every choice of stationary distributions, one for each sufficiently large $r$,
--   $$
--   \frac{Y^r(\infty)-x_*}{\sqrt r} \Rightarrow \mathcal N\big(0,(\beta\gamma)^{-1}\big), \tag{11}
--   $$
--   $$
--   \mathbb E\Big[\frac{Y^r(\infty)-x_*}{\sqrt r}\Big]^+ \to (2\pi\beta\gamma)^{-1/2},\qquad \mathbb E\Big[\frac{Y^r(\infty)-x_*}{\sqrt r}\Big]^- \to (2\pi\beta\gamma)^{-1/2}.
--   $$
--
--   Under the constant base-stock policy ($\gamma=1$) the scaled inventory level has variance $1/\beta$; the GBS policy divides the asymptotic variance by $\gamma$, and with $\gamma = \gamma(r)\to\infty$ (Corollary 2) the scaled average inventory cost vanishes.
--
--   **Formalization Note** The demand rate $r$ is real and tends to $\infty$ along `atTop`. Weak convergence is stated by its definition, through bounded continuous test functions and Mathlib's `gaussianReal` with variance $1/(\beta\gamma)$; expectations are series over states. The page says the chain is irreducible; on $\mathbb Z\times\mathbb Z_+$ that is false (states with $Z<\lceil T(Y)\rceil$ are never entered), and clause 1 states the corrected reading. Positive recurrence is the existence of a stationary distribution (global balance with finite mean exit rate).
-- source:
--   Stolyar and Wang, Exploiting random lead times for significant inventory cost savings, arXiv:1801.02646v6, pp. 10–11, Theorem 1, (11)

import Mathlib
import Definitions.Def_RandomLeadGBS_Diffusion_Model

namespace RandomLeadGBS.Diffusion
open Filter Topology

theorem theorem_1 (P : Params) (hP : P.Standing) :
    (∀ r : ℝ, 0 < r → ∃ s₀ : State, ∀ s : State, Relation.ReflTransGen (Step P r) s s₀) ∧
    (∃ r₀ : ℝ, ∀ r ≥ r₀, ∃! p : State → ℝ, IsStationary P r p) ∧
    ∀ p : ℝ → State → ℝ, (∀ᶠ r in atTop, IsStationary P r (p r)) →
      (∀ g : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun r => ∑' s, p r s * g (scaled P r s)) atTop
          (𝓝 (∫ x, g x ∂(ProbabilityTheory.gaussianReal 0 (1 / (P.β * P.γ)).toNNReal)))) ∧
      Tendsto (fun r => ∑' s, p r s * max (scaled P r s) 0) atTop
        (𝓝 ((2 * Real.pi * P.β * P.γ) ^ (-(1 / 2 : ℝ)))) ∧
      Tendsto (fun r => ∑' s, p r s * max (-(scaled P r s)) 0) atTop
        (𝓝 ((2 * Real.pi * P.β * P.γ) ^ (-(1 / 2 : ℝ)))) := by sorry

end RandomLeadGBS.Diffusion
