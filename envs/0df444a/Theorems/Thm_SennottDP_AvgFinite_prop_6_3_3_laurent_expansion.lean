-- Prove2me | Theorems.Thm_SennottDP_AvgFinite_prop_6_3_3_laurent_expansion
-- name    : SennottDP.AvgFinite.prop_6_3_3_laurent_expansion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T08:58:37.047757+00:00
-- url     : https://prove2.me/theorems/62f83bfd-06b8-4f0e-8b52-8bc8059b0c76
-- title:
--   Proposition 6.3.3 — V_α(i) = J(i)/(1−α) + w*(i) + ε_α(i) with ε_α(i) → 0 as α → 1⁻
-- statement:
--   Assume the hypotheses of Theorem 6.3.1 ($S$ finite, $f$ and $\alpha_0$ as in Proposition 6.2.3, distinguished states $z_k$ in the positive recurrent classes $R_k$ of the chain induced by $f$), and let $w$ be the limit relative value function of Theorem 6.3.1. Let
--   $$w^*(i) = w(i) - \sum_k p_k(i) \Big(\sum_{s \in R_k} \pi_s(f)\, w(s)\Big).$$
--   Then for $i \in S$ and $\alpha \in (0,1)$,
--   $$V_\alpha(i) = \frac{J(i)}{1-\alpha} + w^*(i) + \varepsilon_\alpha(i), \tag{6.21}$$
--   where $\varepsilon_\alpha(i) \to 0$ as $\alpha \to 1^-$.
--
--   This is the first two terms of the expansion of the discounted value function near $\alpha = 1$: the pole is governed by the minimum average cost and the constant term by the normalized relative value function.
--
--   **Formalization Note** The statement asserts that $\varepsilon_\alpha(i) := V_\alpha(i) - J(i)/(1-\alpha) - w^*(i)$ (real valued, via `toReal` of finite quantities) tends to $0$ along `𝓝[<] 1`. $\pi_s(f) = (m_{ss})^{-1}$ are the steady state probabilities of the chain induced by $f$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 106, Proposition 6.3.3, Eq. (6.21)

import Mathlib
import Definitions.Def_SennottDP_AvgFinite_ACOE

namespace SennottDP.AvgFinite

open scoped ENNReal NNReal Topology
open Filter

/-- Proposition 6.3.3 (Sennott, p. 106). Under the hypotheses of Theorem 6.3.1, let
`w*(i) = w(i) − ∑_k p_k(i) (∑_{s ∈ R_k} π_s(f) w(s))`. Then for `i ∈ S` and `α ∈ (0,1)`,
`V_α(i) = J(i)/(1−α) + w*(i) + ε_α(i)` (6.21), where `ε_α(i) → 0` as `α → 1⁻`. -/
theorem prop_6_3_3_laurent_expansion {S : Type*} {Act : Type*} [Fintype S] (M : MDC S Act)
    (f : StationaryPolicy M) (α₀ : ℝ) (hα₀ : α₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hf : ∀ α ∈ Set.Ioo α₀ 1, IsDiscountOptimal f.toPolicy α)
    (Z : Finset S) (hZ : IsDistinguishedSet (inducedChain M f) Z) (i : S) :
    Tendsto
      (fun α : ℝ => (discValue M α i).toReal - (avgValue M i).toReal / (1 - α) -
        relValueNorm M f Z i)
      (𝓝[<] 1) (𝓝 0) := by sorry

end SennottDP.AvgFinite
