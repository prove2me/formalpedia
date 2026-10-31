-- Prove2me | Theorems.Thm_PubFrequency_lemma_EC_5
-- name    : PubFrequency.lemma_EC_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:31:38.062338+00:00
-- url     : https://prove2.me/theorems/476e28ec-3410-4785-80f3-68c3558f1b7c
-- title:
--   Lemma EC.5, p. ec2 — if $\alpha u_1<\alpha u_2\le1$, the pricing game has no pure equilibrium and a mixed one with the stated profits
-- statement:
--   Consider the pricing game of two information publishers with decay rate $\alpha>0$ and fixed cost $k>0$, where $\alpha k<1/2$. The fast firm has cycle $u_1>0$ and the slow firm has cycle $u_2=n\,u_1$ for some $n\in\mathbb N$; customers choose by (3), (4) and (7), and profits are (8). Suppose
--   $$\alpha u_1<\alpha u_2\le1 .$$
--   Then the pricing game has **no** pure-strategy Nash equilibrium, and it has a mixed-strategy Nash equilibrium in the sense of (9) with equilibrium profits
--   $$\pi_1(u_1;u_2)=\frac{\alpha(u_1-2u_2)^2}{16u_2}-\frac{k}{u_1},\qquad \pi_2(u_2;u_1)=\frac{\alpha(u_1+2u_2)^4}{512u_2^3}-\frac{k}{u_2}.$$
--
--   This lemma certifies the closed-form payoffs the publishing game uses when both cycles satisfy $\alpha u\le1$.
--
--   **Formalization Note** The profits are stated with the same definitions (`fastEC5`, `slowEC5`) as the publishing game's payoffs.
--
--   Differences from the source:
--   - encoding: u₂/u₁ ∈ ℕ (p. 9), D = {i·u₁/u₂ | i = 0, …, u₂/u₁} → u₂ = n·u₁ with n : ℕ, D = {i/n | i ≤ n}; reason: the same instances
--   - reading: (7): d̃*(1; r, u) := argmin_{j∈[0,u₂/u₁]} |∂U(j u₁/u₂, 1; r, u)/∂d| in the region w = 1, ∂U(0,1)/∂d ≥ 0, U(1,1) < U(1 − u₁/u₂, 1) → d̃* = (u₁/u₂)·j*, where j* is the largest minimizer over the real interval [0, n] (sSup of the minimizer set) and ∂U/∂d is Lean's deriv of d ↦ U(d, 1; r); reason: (7) writes the count j; the proof of Lemma EC.10 (EC.27, p. ec9) scales it by u₁/u₂; footnote 9 (p. ec1) selects the largest minimizer
--   - reading: d*(w; r, u) := argmax_{d∈D} U(d, w; r, u) with the tie rule of (4) stated for portfolios with the weekly → the largest maximizer over D for both w = 1 and w = 0; reason: for w = 1 this is (4)'s rule; for w = 0 the paper states none, and the same 'more to less' rule (footnote 9) is used
--   - reading: w̃*(r, u) := argmax_{w∈{0,1}} U(d̃*(w; r, u), w; r, u), with no tie rule stated for w̃* → wTilde = 1 on a tie; reason: (4)'s tie rule selects the portfolio with the weekly, and the proofs use it (r₂ ≤ Λ gives w = 1 in (EC.2), (EC.14))
--   - encoding: w ∈ {0, 1} in (3), (4) and (7) → w : ℝ in U, dStar and dTildeW, evaluated only at 0 and 1 (wTilde takes only these values); reason: the same instances
--   - reading: (9): supports Sᵢ and cdfs Fᵢ with Πᵢ(rᵢ; F₋ᵢ) = Π*ᵢ on Sᵢ and ≤ Π*ᵢ off Sᵢ → probability measures μᵢ on ℝ with μᵢ(Sᵢᶜ) = 0, concentrated on a bounded interval, with r' ↦ Πᵢ(r; r') integrable against μ₋ᵢ for every r, and the two conditions at every real price; reason: a cdf is represented by its law; integrability rules out Lean's junk value ∫ = 0 for non-integrable integrands; the added conditions only restrict the witness, and the paper's equilibrium distributions (EC.35)–(EC.38) are bounded
-- source:
--   Chen–Roels, Fast or Slow? Competing on Publication Frequency, SSRN 3986163 (INSEAD WP 2021/74/TOM, 2021), Lemma EC.5, p.ec2 (PDF 31)

import Mathlib
import Definitions.Def_PubFrequency_MixedEquilibrium
import Definitions.Def_PubFrequency_PricingGame
import Definitions.Def_PubFrequency_PublishingGame

namespace PubFrequency

/-- **Lemma EC.5**, Chen–Roels, *Fast or Slow? Competing on Publication Frequency*, SSRN 3986163
(INSEAD WP 2021/74/TOM), p. ec2 (PDF 31). Let `α > 0`, `k > 0` with `α k < 1/2`, fast cycle
`u₁ > 0` and slow cycle `u₂ = n u₁` with `n : ℕ`, and suppose `α u₁ < α u₂ ≤ 1`. Then the pricing
game with profits (8) has no pure-strategy equilibrium, and it has a mixed-strategy equilibrium
(9) with profits `π₁ = α(u₁ − 2u₂)²/(16u₂) − k/u₁` (`fastEC5`) and
`π₂ = α(u₁ + 2u₂)⁴/(512u₂³) − k/u₂` (`slowEC5`).

**Formalization Note.** The cycle ratio is `n : ℕ`; the hypotheses force `n ≥ 2`. The profits are
the same definitions the publishing game's payoffs use in this regime. -/
theorem lemma_EC_5 (α k u₁ : ℝ) (n : ℕ) (hα : 0 < α) (hk : 0 < k) (hαk : α * k < 1 / 2)
    (hu₁ : 0 < u₁) (h₁ : α * u₁ < α * ((n : ℝ) * u₁)) (h₂ : α * ((n : ℝ) * u₁) ≤ 1) :
    (¬ ∃ r₁ r₂ : ℝ, IsPureEq (profit1 α k u₁ n) (profit2 α k u₁ n) r₁ r₂) ∧
    IsMixedEqWithProfits (profit1 α k u₁ n) (profit2 α k u₁ n)
      (fastEC5 α k u₁ ((n : ℝ) * u₁)) (slowEC5 α k u₁ ((n : ℝ) * u₁)) := by sorry

end PubFrequency
