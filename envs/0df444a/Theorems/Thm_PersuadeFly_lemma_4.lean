-- Prove2me | Theorems.Thm_PersuadeFly_lemma_4
-- name    : PersuadeFly.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:29:50.700009+00:00
-- url     : https://prove2.me/theorems/c79931a4-0f8f-43b8-a84a-4c447c482f35
-- title:
--   Lemma 4, p.40 — $|V(\mu_1,\sigma)-V(\mu_2,\sigma)|\le\frac12\|\mu_1-\mu_2\|_1$
-- statement:
--   Let $\mu_1,\mu_2\in\Delta(\Omega)$ and let $\sigma$ be any signaling mechanism (persuasive or not). Then
--   $$
--   |V(\mu_1,\sigma)-V(\mu_2,\sigma)|\le\frac12\,\|\mu_1-\mu_2\|_1 .
--   $$
--   The sender's expected utility is Lipschitz in the prior, uniformly over mechanisms. This bounds the error from evaluating a mechanism under the empirical distribution instead of the true one.
--
--   Differences from the source: none.
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, Lemma 4, p.40

import Mathlib
import Definitions.Def_PersuadeFly_value
import Definitions.Def_PersuadeFly_IsMechanism
import Definitions.Def_PersuadeFly_l1Dist

namespace PersuadeFly

/-- **Lemma 4.** Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, Lemma 4, p.40: for any `μ₁, μ₂ ∈ Δ(Ω)` and any signaling mechanism `σ`,
`|V(μ₁, σ) − V(μ₂, σ)| ≤ ½ ‖μ₁ − μ₂‖₁`. -/
theorem lemma_4 {Ω A : Type} [Fintype Ω] [Nontrivial Ω] [Fintype A] [Nontrivial A]
    (I : Instance Ω A) (μ1 μ2 : Ω → ℝ) (hμ1 : μ1 ∈ stdSimplex ℝ Ω) (hμ2 : μ2 ∈ stdSimplex ℝ Ω)
    (σ : Ω → A → ℝ) (hσ : IsMechanism σ) :
    |value I μ1 σ - value I μ2 σ| ≤ 1 / 2 * l1Dist μ1 μ2 := by sorry

end PersuadeFly
