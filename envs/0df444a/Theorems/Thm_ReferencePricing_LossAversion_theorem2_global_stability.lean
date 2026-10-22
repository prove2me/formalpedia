-- Prove2me | Theorems.Thm_ReferencePricing_LossAversion_theorem2_global_stability
-- name    : ReferencePricing.LossAversion.theorem2_global_stability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T08:50:14.848221+00:00
-- url     : https://prove2.me/theorems/ccd1ef07-049f-4356-91d8-8da15a2ebdb2
-- title:
--   Theorem 2 — a unique steady state exists, all optimal price paths converge to it, reference paths monotonically
-- statement:
--   Consider the loss-neutral problem (2) on $P=[0,\bar p]$ with $\alpha\in[0,1)$ and $\beta\in(0,1)$, under Assumptions 1–3 and with $d$ differentiable. Then:
--
--   1. problem (2) has exactly one steady state $p^{**}$;
--   2. $p^{**}$ solves equation (3) of Theorem 1, $\pi'(p)/(1-\beta)=p\lambda(p)/(1-\alpha\beta)$;
--   3. for every initial reference price $r_0\in P$, the optimal price path $p^*_t$ converges to $p^{**}$, and the optimal reference price path $r^*_t$ is monotone (nondecreasing or nonincreasing) and converges to $p^{**}$:
--   $$
--   \lim_{t\to\infty}p^*_t=\lim_{t\to\infty}r^*_t=p^{**}.
--   $$
--
--   This is global stability of the loss-neutral problem. In the loss-averse case it is applied to the smooth problems $(P_L)$ and $(P_G)$, whose steady states $p^{**}_L$ and $p^{**}_G$ bound the set of steady states of the kinked problem.
--
--   **Formalization Note** Existence of the steady state is part of the conclusion, not a hypothesis. Paths are defined with the largest-maximizer policy of the paper. The hypothesis that $d$ is differentiable is added (see Theorem 1).
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 419, Theorem 2 (proof in Appendix A.6, p. 426)

import Mathlib
import Definitions.Def_RobustBooking_Shared_optPrice
import Definitions.Def_RobustBooking_Shared_Assumptions
open RobustBooking.Shared

open Filter Topology

namespace ReferencePricing.LossAversion

/-- Theorem 2 (Global Stability and State-Path Monotonicity), Popescu and Wu 2007, p. 419: under
Assumptions 1–3 problem (2) admits a unique steady state `p**`, characterized by (3) of
Theorem 1; from every initial reference price `r₀ ∈ P` the optimal price path converges to
`p**`, and the reference (state) path converges to `p**` monotonically. -/
theorem theorem2_global_stability (pbar α β : ℝ) (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hd : Differentiable ℝ d) (hA1 : Assumption1 pbar d R) (hA2 : Assumption2 R)
    (hA3 : Assumption3 pbar d R) :
    ∃ p : ℝ, IsSteadyState (profit d R) α β pbar p ∧
      (∀ q : ℝ, IsSteadyState (profit d R) α β pbar q → q = p) ∧
      deriv (baseProfit d) p / (1 - β) = p * refSlope R p / (1 - α * β) ∧
      ∀ r₀ ∈ Set.Icc (0 : ℝ) pbar,
        Tendsto (pricePath (profit d R) α β pbar r₀) atTop (𝓝 p) ∧
        (Monotone (statePath (profit d R) α β pbar r₀) ∨
          Antitone (statePath (profit d R) α β pbar r₀)) ∧
        Tendsto (statePath (profit d R) α β pbar r₀) atTop (𝓝 p) := by sorry

end ReferencePricing.LossAversion
