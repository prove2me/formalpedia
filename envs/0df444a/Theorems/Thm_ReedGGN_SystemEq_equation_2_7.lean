-- Prove2me | Theorems.Thm_ReedGGN_SystemEq_equation_2_7
-- name    : ReedGGN.SystemEq.equation_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:49:45.815798+00:00
-- url     : https://prove2.me/theorems/cc74a6e9-eb5f-4b8a-ba15-59e8277f56ea
-- title:
--   (2.7), p. 7 — Q(t) = I(t) + W₀(t) + M₂(t) + A_G(t) + Σ (G(t − w̃ᵢ) − G(t)) + Σ (G(t − τᵢ − wᵢ) − G(t − τᵢ))
-- statement:
--   Let $F$ and $F_0$ be the service-time and residual service-time distributions, with tails $G=1-F$ and $\bar F_0=1-F_0$, and fix a sample path of the $G/GI/N$ queue. With $Q$ the number in system (2.2) and $W_0$, $M_2$, $A_G$, $I$ as in (2.4)–(2.6) and p. 7, for every $t\ge0$,
--   $$Q(t)=I(t)+W_0(t)+M_2(t)+A_G(t)+\sum_{i=1}^{(Q_0-N)^+}\big(G(t-\tilde w_i)-G(t)\big)+\sum_{i=1}^{A(t)}\big(G(t-\tau_i-w_i)-G(t-\tau_i)\big).$$
--
--   The paper obtains it from (2.2) by centring each indicator at its (conditional) mean, which gives (2.3), and then adding and subtracting $A_G(t)$ and $(Q_0-N)^+G(t)$. It separates the number in system into a mean term for the initial customers, two fluctuation terms, the infinite-server mean $A_G$, and two corrections due to waiting; Proposition 2.1 rewrites the corrections.
--
--   **Formalization Note** The identity is pathwise and uses no property of the waiting times; $F$ and $F_0$ are probability measures $\mu,\mu_0$ on $\mathbb R$.
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, p. 7, Eq. (2.7) (via (2.3))

import Mathlib
import Definitions.Def_ReedGGN_SystemEq_QueueLength

namespace ReedGGN.SystemEq

open MeasureTheory

/-- Equation (2.7) (p. 7): the number in system (2.2) decomposes as
`Q(t) = I(t) + W₀(t) + M₂(t) + A_G(t) + Σ_{i=1}^{(Q₀−N)⁺} (G(t − w̃_i) − G(t))
          + Σ_{i=1}^{A(t)} (G(t − τ_i − w_i) − G(t − τ_i))`. -/
theorem equation_2_7 (μ μ₀ : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ₀]
    (P : SamplePath) (t : ℝ) (ht : 0 ≤ t) :
    (Q P t : ℝ) =
      I μ μ₀ P t + W0 μ₀ P t + M2 μ P t + AG μ P t +
        (∑ i ∈ Finset.Icc 1 (P.Q₀ - P.N), (G μ (t - P.wt i) - G μ t)) +
        ∑ i ∈ Finset.Icc 1 (P.A t), (G μ (t - P.τ i - P.w i) - G μ (t - P.τ i)) := by sorry

end ReedGGN.SystemEq
