-- Prove2me | Theorems.Thm_PricingRM_DetHeuristic_ce_upper_bound
-- name    : PricingRM.DetHeuristic.ce_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:33:47.478481+00:00
-- url     : https://prove2.me/theorems/f452cb5f-320d-40c6-8acb-e500f431176b
-- title:
--   Eq. (24) — the certainty-equivalent value bounds the single-price optimal revenue
-- statement:
--   Consider a single selling period (the single-price model of §3.1–3.2.1): at price $p \ge 0$ the demand $D(p)$ is a nonnegative random variable with finite mean, and with capacity $C$ the revenue is $p\min\{D(p), C\}$. Let
--   $$
--   V(C) = \sup_{p\ge 0} E\big[p\min\{D(p), C\}\big] \quad\text{(eq. (22))}, \qquad V^{\det}(C) = \sup_{p \ge 0} p\min\{E[D(p)], C\} \quad\text{(eq. (24))}.
--   $$
--   Then for every price $p \ge 0$,
--   $$
--   E\big[p\min\{D(p), C\}\big] \le p\min\{E[D(p)], C\},
--   $$
--   and consequently $V(C) \le V^{\det}(C)$.
--
--   The certainty-equivalent problem replaces the random demand by its mean; this bound says it overestimates the optimal expected revenue. It is also the one-period case of Proposition 8's first assertion.
--
--   **Formalization Note** The single-period model is the mission's `PricingModel` with $N = 1$; $V(C)$ is its Bellman value `optValue`, and $V^{\det}(C)$ is `ceValue`, both suprema in $[0,\infty]$ (the paper writes $\max$). The $V^{\det}$ of (24) is a different object from the constrained $V_1^{\det}$ of (32)–(33) and is kept separate.
-- source:
--   Bitran and Caldentey, An Overview of Pricing Models for Revenue Management, MSOM 5(3) 2003, p. 217, eqs. (22) and (24)

import Mathlib
import Definitions.Def_PricingRM_DetHeuristic_PricingModel

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PricingRM.DetHeuristic

/-- Bitran–Caldentey (2003), eq. (24), p. 217: in a single-period model, for every price `p ≥ 0`,
`E[p·min{D(p), C}] ≤ p·min{E[D(p)], C}`, and hence the optimal expected revenue
`V(C) = ⨆_{p ≥ 0} E[p·min{D(p), C}]` of (22) is at most the certainty-equivalent value
`V^det(C) = ⨆_{p ≥ 0} p·min{E[D(p)], C}`. -/
theorem ce_upper_bound (M : PricingModel 1) (C : ℝ) :
    (∀ p : ℝ, 0 ≤ p → ∫ x, p * min x C ∂(M.μ 0 p) ≤ p * min (meanDemand M 0 p) C) ∧
      optValue M C ≤ ceValue M 0 C := by sorry

end PricingRM.DetHeuristic
