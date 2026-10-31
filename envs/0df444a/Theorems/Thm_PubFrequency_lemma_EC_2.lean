-- Prove2me | Theorems.Thm_PubFrequency_lemma_EC_2
-- name    : PubFrequency.lemma_EC_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:31:36.595157+00:00
-- url     : https://prove2.me/theorems/5629ef61-ad74-4841-a640-cdcbe253dd03
-- title:
--   Lemma EC.2, p. ec1 — if $\alpha u_1\le1<\alpha u_2$, the pricing game has no pure equilibrium and a mixed one with profits (EC.3)
-- statement:
--   Consider the pricing game of two information publishers with decay rate $\alpha>0$ and fixed cost $k>0$, where $\alpha k<1/2$. The fast firm has cycle $u_1>0$ and the slow firm has cycle $u_2=n\,u_1$ for some $n\in\mathbb N$; customers choose dailies and the weekly by (3), (4) and (7), and the firms' profits are (8). Suppose
--   $$\alpha u_1\le 1<\alpha u_2 .$$
--   Then:
--   1. the pricing game has **no** pure-strategy Nash equilibrium;
--   2. it has a mixed-strategy Nash equilibrium in the sense of (9) whose equilibrium profits are (EC.3):
--   $$\pi_1(u_1;u_2)=\begin{cases}\dfrac{\alpha(u_1-2u_2)^2}{16u_2}-\dfrac{k}{u_1},&u_1\le\dfrac{4-2\alpha u_2}{\alpha},\\[2mm]\dfrac{(2-\alpha u_1)(\alpha u_2-1)}{2\alpha u_2}-\dfrac{k}{u_1},&\text{otherwise},\end{cases}\qquad
--   \pi_2(u_2;u_1)=\begin{cases}\dfrac{\alpha(u_1+2u_2)^4}{512u_2^3}-\dfrac{k}{u_2},&u_2\le\dfrac{4-\alpha u_1}{2\alpha},\\[2mm]\dfrac{(\alpha u_1+2\alpha u_2-2)^2}{8\alpha^3u_2^3}-\dfrac{k}{u_2},&\text{otherwise}.\end{cases}$$
--
--   This lemma certifies that the closed-form payoffs the publishing game uses in the regime $\alpha u_f\le1<\alpha u_s$ are genuine pricing-equilibrium profits.
--
--   **Formalization Note** The profits are stated with the same definitions (`fastEC3`, `slowEC3`) as the publishing game's payoffs.
--
--   Differences from the source:
--   - encoding: u₂/u₁ ∈ ℕ (p. 9), D = {i·u₁/u₂ | i = 0, …, u₂/u₁} → u₂ = n·u₁ with n : ℕ, D = {i/n | i ≤ n}; reason: the same instances
--   - reading: (7): d̃*(1; r, u) := argmin_{j∈[0,u₂/u₁]} |∂U(j u₁/u₂, 1; r, u)/∂d| in the region w = 1, ∂U(0,1)/∂d ≥ 0, U(1,1) < U(1 − u₁/u₂, 1) → d̃* = (u₁/u₂)·j*, where j* is the largest minimizer over the real interval [0, n] (sSup of the minimizer set) and ∂U/∂d is Lean's deriv of d ↦ U(d, 1; r); reason: (7) writes the count j; the proof of Lemma EC.10 (EC.27, p. ec9) scales it by u₁/u₂; footnote 9 (p. ec1) selects the largest minimizer
--   - reading: d*(w; r, u) := argmax_{d∈D} U(d, w; r, u) with the tie rule of (4) stated for portfolios with the weekly → the largest maximizer over D for both w = 1 and w = 0; reason: for w = 1 this is (4)'s rule; for w = 0 the paper states none, and the same 'more to less' rule (footnote 9) is used
--   - reading: w̃*(r, u) := argmax_{w∈{0,1}} U(d̃*(w; r, u), w; r, u), with no tie rule stated for w̃* → wTilde = 1 on a tie; reason: (4)'s tie rule selects the portfolio with the weekly, and the proofs use it (r₂ ≤ Λ gives w = 1 in (EC.2), (EC.14))
--   - encoding: w ∈ {0, 1} in (3), (4) and (7) → w : ℝ in U, dStar and dTildeW, evaluated only at 0 and 1 (wTilde takes only these values); reason: the same instances
--   - reading: (9): supports Sᵢ and cdfs Fᵢ with Πᵢ(rᵢ; F₋ᵢ) = Π*ᵢ on Sᵢ and ≤ Π*ᵢ off Sᵢ → probability measures μᵢ on ℝ with μᵢ(Sᵢᶜ) = 0, concentrated on a bounded interval, with r' ↦ Πᵢ(r; r') integrable against μ₋ᵢ for every r, and the two conditions at every real price; reason: a cdf is represented by its law; integrability rules out Lean's junk value ∫ = 0 for non-integrable integrands; the added conditions only restrict the witness, and the paper's equilibrium distributions (EC.35)–(EC.38) are bounded
--   - reading: (EC.3) labels the slow firm's profit 'π2(u1;u2)' → slowEC3 α k u₁ u₂ is Firm 2's profit π₂(u₂; u₁); reason: a label typo; Lemma EC.5 and (EC.54) write π₂(u₂; u₁)
-- source:
--   Chen–Roels, Fast or Slow? Competing on Publication Frequency, SSRN 3986163 (INSEAD WP 2021/74/TOM, 2021), Lemma EC.2, eq. (EC.3), p.ec1 (PDF 30)

import Mathlib
import Definitions.Def_PubFrequency_MixedEquilibrium
import Definitions.Def_PubFrequency_PricingGame
import Definitions.Def_PubFrequency_PublishingGame

namespace PubFrequency

/-- **Lemma EC.2**, Chen–Roels, *Fast or Slow? Competing on Publication Frequency*, SSRN 3986163
(INSEAD WP 2021/74/TOM), p. ec1 (PDF 30). Let `α > 0`, `k > 0` with `α k < 1/2`, fast cycle
`u₁ > 0` and slow cycle `u₂ = n u₁` with `n : ℕ`, and suppose `α u₁ ≤ 1` and `α u₂ > 1`. Then the
pricing game with profits (8) has no pure-strategy equilibrium, and it has a mixed-strategy
equilibrium (9) whose equilibrium profits are (EC.3): `fastEC3 α k u₁ u₂` for the fast firm and
`slowEC3 α k u₁ u₂` for the slow firm.

**Formalization Note.** The cycle ratio is `n : ℕ` (the paper's integrality restriction, p. 9);
the regime hypotheses force `n ≥ 2`. The profits (EC.3) are the same definitions the publishing
game's payoffs use in this regime. -/
theorem lemma_EC_2 (α k u₁ : ℝ) (n : ℕ) (hα : 0 < α) (hk : 0 < k) (hαk : α * k < 1 / 2)
    (hu₁ : 0 < u₁) (h₁ : α * u₁ ≤ 1) (h₂ : 1 < α * ((n : ℝ) * u₁)) :
    (¬ ∃ r₁ r₂ : ℝ, IsPureEq (profit1 α k u₁ n) (profit2 α k u₁ n) r₁ r₂) ∧
    IsMixedEqWithProfits (profit1 α k u₁ n) (profit2 α k u₁ n)
      (fastEC3 α k u₁ ((n : ℝ) * u₁)) (slowEC3 α k u₁ ((n : ℝ) * u₁)) := by sorry

end PubFrequency
