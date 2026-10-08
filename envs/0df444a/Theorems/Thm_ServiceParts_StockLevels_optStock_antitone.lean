-- Prove2me | Theorems.Thm_ServiceParts_StockLevels_optStock_antitone
-- name    : ServiceParts.StockLevels.optStock_antitone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T07:28:52.193967+00:00
-- url     : https://prove2.me/theorems/ed6fea8b-423b-49d3-bdb7-fd3997b7edca
-- title:
--   Section 3.4.2, p. 61 — s*(θ) and the investment C(θ) are nonincreasing in θ
-- statement:
--   Consider $n$ item types with compound Poisson demand, expected backorders $B_i$, mean lead-time demands $\mu_i$ and unit costs $c_i > 0$. For a multiplier $\theta > 0$ let $s_i^*(\theta)$ be the smallest stock level with
--   $$\sum_{x \le s} p(x \mid \mu_i) \ge \frac{1}{1 + \theta c_i},$$
--   and let
--   $$C(\theta) = \sum_{i=1}^n c_i\,\big[s_i^*(\theta) - \mu_i + B_i(s_i^*(\theta))\big].$$
--   If $0 < \theta_1 \le \theta_2$, then $s_i^*(\theta_2) \le s_i^*(\theta_1)$ for every $i$, and $C(\theta_2) \le C(\theta_1)$.
--
--   The investment $C(\theta)$ therefore moves monotonically with the multiplier, which is what makes a bisection on $\theta$ meaningful when searching for a budget $b$.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 61, Section 3.4.2 (monotonicity of s*(θ) and C(θ)); p. 63

import Mathlib
import Definitions.Def_ServiceParts_StockLevels_CompoundPoissonDemand
import Definitions.Def_ServiceParts_StockLevels_Problems

namespace ServiceParts.StockLevels

theorem optStock_antitone {ι : Type*} [Fintype ι] (d : ι → CompoundPoissonDemand)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) (θ₁ θ₂ : ℝ) (hθ₁ : 0 < θ₁) (hθ : θ₁ ≤ θ₂)
    (s₁ s₂ : ι → ℕ) (hs₁ : ∀ i, IsLeast (stockSet (d i) (c i) θ₁) (s₁ i))
    (hs₂ : ∀ i, IsLeast (stockSet (d i) (c i) θ₂) (s₂ i)) :
    (∀ i, s₂ i ≤ s₁ i) ∧ totalInvestment d c s₂ ≤ totalInvestment d c s₁ := by sorry

end ServiceParts.StockLevels
