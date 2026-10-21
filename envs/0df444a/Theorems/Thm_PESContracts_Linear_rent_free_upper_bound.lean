-- Prove2me | Theorems.Thm_PESContracts_Linear_rent_free_upper_bound
-- name    : PESContracts.Linear.rent_free_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:10:30.033864+00:00
-- url     : https://prove2.me/theorems/25834ba7-ccfc-46df-89df-27fb74f71180
-- title:
--   Equations (4)–(5), p. 10 — information-rent-free payoff bound
-- statement:
--   Let a direct revelation contract $(a,P)$ satisfy the action bounds, nonnegative payments, individual rationality, and incentive compatibility of §2.1. For a probability distribution $\mu$ supported on the type interval, and integrable action and payment functions, its actual expected payoff satisfies
--
--   $$
--   \mathbb E_\mu[k a(\theta)-P(\theta)]
--   \leq\mathbb E_\mu[k a(\theta)-c_h(a(\theta)-\theta a_0)].
--   $$
--
--   The right side removes the agent's information rent and bounds the payoff of every feasible contract, including an optimal one.
--
--   **Formalization Note** The paper writes the bound for optimal contract quantities using a density and virtual-surplus expression. This statement gives the same upper-bound step for every feasible direct contract, so it also covers atomic type laws. Integrability makes the expected actual payoff well defined.
-- source:
--   Li, Ashlagi & Lo, Simple and Approximately Optimal Contracts for Payment for Ecosystem Services, SSRN preprint 3754041 (version of 2021-05-19), p. 10, Equations (4)–(5), and p. 24, Appendix A.4; https://ssrn.com/abstract=3754041

import Mathlib
import Definitions.Def_PESContracts_Linear_Model
open MeasureTheory

namespace PESContracts.Linear

/-- Equations (4)–(5), p. 10: removing the information rent bounds the actual payoff. -/
theorem rent_free_upper_bound (M : Params) (hM : M.Standing) (k : ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ M.typesᶜ = 0)
    (C : DirectContract) (hC : C.Feasible M)
    (ha : Integrable C.a μ) (hP : Integrable C.P μ) :
    C.payoff k μ ≤
      ∫ θ, (k * C.a θ - cost M.h (C.a θ - θ * M.a0)) ∂μ := by sorry

end PESContracts.Linear
