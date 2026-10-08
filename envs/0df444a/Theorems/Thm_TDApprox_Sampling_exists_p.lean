-- Prove2me | Theorems.Thm_TDApprox_Sampling_exists_p
-- name    : TDApprox.Sampling.exists_p
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:24:29.931906+00:00
-- url     : https://prove2.me/theorems/1602ad61-bbfb-4820-840a-28b975127883
-- title:
--   §9, p. 24 — existence of the positive transition distribution
-- statement:
--   Fix two distinct states $s_1,s_2$ in a countable state space and a discount factor $5/6<\alpha<1$. There is a probability distribution $p$ assigning positive mass to every state such that
--
--   $$\frac{5}{6\alpha}<p(s_2)<1.$$
--
--   This supplies the transition distribution used in the paper's divergence example, including when the state space is countably infinite.
--
--   **Formalization Note** The state $s_2$ represents state 2 in the paper's indexing. The probability distribution is a measure with positive singleton masses.
-- source:
--   Tsitsiklis & Van Roy, LIDS-P-2322 (1996), Theorem 3 proof, p. 24; https://dspace.mit.edu/entities/publication/ab395d25-a6d3-407a-9589-60eaac58fd05

import Mathlib
import Definitions.Def_TDApprox_Sampling_Model

namespace TDApprox.Sampling

open MeasureTheory

theorem exists_p
    {S : Type*} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (s₁ s₂ : S) (hne : s₁ ≠ s₂) (α : ℝ)
    (hα₁ : (5 : ℝ) / 6 < α) (hα₂ : α < 1) :
    ∃ p : Measure S, ∃ _ : IsProbabilityMeasure p,
      (∀ i, 0 < p {i}) ∧
      5 / (6 * α) < (p {s₂}).toReal ∧
      (p {s₂}).toReal < 1 := by sorry

end TDApprox.Sampling
