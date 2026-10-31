-- Prove2me | Theorems.Thm_PubFrequency_lemma_EC_3
-- name    : PubFrequency.lemma_EC_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:30:54.79421+00:00
-- url     : https://prove2.me/theorems/23d7093b-450a-43bf-bdf1-8366d44d2a54
-- title:
--   Lemma EC.3, p. ec2 — in every equilibrium of the publishing game, the faster cycle satisfies $\alpha u_1^*\le1$
-- statement:
--   Let $\alpha>0$, $k>0$ with $\alpha k<1/2$, and let $(u_1^*,u_2^*)$ be a pure-strategy Nash equilibrium of the publishing game (10), in which each firm chooses a positive cycle, equal to its rival's or at least twice or at most half of it, to maximize its anticipated pricing-equilibrium profit. If
--   $$u_1^*\le u_2^*,\qquad\text{then}\qquad \alpha u_1^*\le1 .$$
--
--   In equilibrium the fast publisher releases its issue before its information stock reaches the steady state of (1). This pins down the regime in which the equilibrium cycles are computed.
--
--   Differences from the source:
--   - reading: 'Suppose that u∗1 ≤ u∗2' with u∗ an equilibrium of (10) left implicit → (u₁, u₂) is an explicit hypothesis IsPubEq α k u₁ u₂; reason: the proof ('any strategy u1 > 1/α is strictly dominated') is about equilibria of (10)
--   - reading: (10)'s payoff πᵢ(uᵢ; u₋ᵢ) is Firm i's pricing-equilibrium profit Π*ᵢ(u), with the integer-ratio constraint relaxed (p. 12) → pay: the paper's closed-form equilibrium profits at β = 1 for every real pair of positive cycles — Lemma EC.5 if both cycles are ≤ 1/α, (EC.3) if αu_f ≤ 1 < αu_s, (EC.48) if αu_f > 1, and −k/u on equal cycles ((EC.55)); reason: the pricing game needs u₂/u₁ ∈ ℕ and is undefined at the relaxed cycles; the proof of Theorem 3 (pp. ec21–ec22) uses π only through these closed forms; Lemmas EC.2 and EC.5 tie them to the pricing game at integer ratios
--   - reading: at αu_f = 1 both (EC.3) (hypothesis αu₁ ≤ 1) and (EC.48) (hypothesis u₂ ≥ u₁ ≥ 1/α) apply and give different slow-firm profits → the (EC.3)/Lemma EC.5 branch is used whenever αu_f ≤ 1, (EC.48) only when αu_f > 1; reason: this is how the proof of Theorem 3 applies them ((EC.53)–(EC.54) for αu₁ ≤ 1, (EC.48) only to dominate u₁ > 1/α)
--   - reading: u*ᵢ = argmax over the feasible set in (10) → u*ᵢ is a maximizer of its payoff over the feasible set (IsPubEq); reason: the Nash-equilibrium condition; the paper's proof checks only that no feasible deviation is profitable (p. ec28)
--   - encoding: uᵢ > 0 with max{uᵢ, u*₋ᵢ}/min{uᵢ, u*₋ᵢ} ≥ 2 if uᵢ ≠ u*₋ᵢ → Feasible u u' := 0 < u ∧ (u = u' ∨ 2u ≤ u' ∨ 2u' ≤ u); reason: the same set for positive cycles, written without division
-- source:
--   Chen–Roels, Fast or Slow? Competing on Publication Frequency, SSRN 3986163 (INSEAD WP 2021/74/TOM, 2021), Lemma EC.3, p.ec2 (PDF 31)

import Mathlib
import Definitions.Def_PubFrequency_PublishingGame

namespace PubFrequency

/-- **Lemma EC.3**, Chen–Roels, *Fast or Slow? Competing on Publication Frequency*, SSRN 3986163
(INSEAD WP 2021/74/TOM), p. ec2 (PDF 31): "Suppose that u∗1 ≤ u∗2. Then, αu∗1 ≤ 1." Here
`(u₁, u₂)` is any pure-strategy equilibrium of the publishing game (10) with `α > 0`, `k > 0`,
`α k < 1/2`. -/
theorem lemma_EC_3 (α k : ℝ) (hα : 0 < α) (hk : 0 < k) (hαk : α * k < 1 / 2)
    (u₁ u₂ : ℝ) (heq : IsPubEq α k u₁ u₂) (hle : u₁ ≤ u₂) :
    α * u₁ ≤ 1 := by sorry

end PubFrequency
