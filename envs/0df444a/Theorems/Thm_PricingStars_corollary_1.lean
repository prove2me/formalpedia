-- Prove2me | Theorems.Thm_PricingStars_corollary_1
-- name    : PricingStars.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:30:28.698374+00:00
-- url     : https://prove2.me/theorems/f635cad6-78be-4dce-a751-e7aa48fe76b1
-- title:
--   Corollary 1 — comparative statics in the rating sensitivity $\sigma$ (corrected: $\kappa>1/2$ for “otherwise”)
-- statement:
--   Fix a seller of type $\theta>-1$, a discount factor $\delta\in(0,1)$ and a price internalization $\kappa\in[0,1)$. Let $\tilde\Psi(\sigma)$, $\tilde p(\sigma)$ be the long-run rating and price of the seller's problem at sensitivity $\sigma$: the limits of the ratings and prices along every optimal plan from every initial rating. Then such functions exist on the admissible set $S(\kappa)$, and for every such pair, at every $\sigma\in S(\kappa)$ (derivatives taken within $S(\kappa)$):
--
--   1. **(a) prices:** $\dfrac{d\tilde p}{d\sigma}>0$ when $\kappa<\tfrac12$, and $\dfrac{d\tilde p}{d\sigma}<0$ when $\kappa>\tfrac12$;
--   2. **(b) consumer surplus:** with $\widetilde{CS}(\sigma)=\int_{\tilde\omega(\tilde\Psi,\tilde p)}^{1}(\theta+\omega-\tilde p)\,d\omega$, $\dfrac{d\widetilde{CS}}{d\sigma}<0$ when $\kappa<\tfrac12$, and $\dfrac{d\widetilde{CS}}{d\sigma}>0$ when $\kappa>\tfrac12$;
--   3. **(c) profits:** with $\tilde\pi(\sigma)=\tilde p\,q(\tilde\Psi,\tilde p)$, $\dfrac{d\tilde\pi}{d\sigma}>0$ when $\kappa\neq\tfrac12$;
--   4. **(d) ratings:** $\tilde\Psi$ is increasing on $S(\kappa)$; when $\kappa\neq\tfrac12$, moreover $\dfrac{d\tilde\Psi}{d\sigma}>0$ and $\tilde\Psi$ is strictly increasing.
--
--   A more sensitive rating system thus always helps the seller, raises the long-run rating, and hurts consumers exactly when reviews internalize little of the price.
--
--   **Formalization Note** The long-run objects are defined through the seller's optimal plans (`IsLongRunOutcome`), not through the closed forms (28)–(29); the statement asserts their existence as well as the signs, so it is not vacuous. At $\sigma=1$ (possible when $\kappa<1/2$) the derivative is one-sided.
--
--   Differences from the source:
--   - correction: (a) dp̃/dσ < 0 'otherwise' and (b) dC̃S/dσ > 0 'otherwise', i.e. for κ ≥ 1/2 → only for κ > 1/2; reason: at κ = 1/2 and any σ ∈ (0,1), δ, θ > −1, (28)–(29) give Ψ̃ = p̃ = (θ+1)/2 independent of σ, so both derivatives are 0
--   - correction: technical assumption: σ < 1 − κ only when κ > 1/2 (p.7), so (κ, σ) = (1/2, 1) is allowed; footnote 12 claims κ < max{1/2, 1 − σ} holds → the admissible set also excludes the single point (κ, σ) = (1/2, 1); reason: there the price does not move the review and ψ̄' = θ + 1 − ψ̄; at θ = 0, δ = 1/2, ψ̄₀ = 0 the unique optimal plan is myopic and the ratings run 0, 1, 0, 1, …, so no long-run limit exists and b = −1
--   - reading: (b) 'dC̃S/dm > 0' → dC̃S/dσ > 0; reason: m appears nowhere else in §3; a typo for σ
--   - reading: long-run consumer surplus C̃S (not defined in the paper) → ∫ from ω̃(Ψ̃, p̃) to 1 of (θ + ω − p̃) dω, the purchasers' true surplus at the long-run rating and price; reason: p.14 ties C̃S to the cutoff type at the long-run price; this reading reproduces the paper's (71) with β = 1
--   - reading: (d) 'Ψ̃ is increasing in σ' → MonotoneOn Ψ̃ on S(κ); reason: at κ = 1/2, Ψ̃ = (θ+1)/2 is constant, so only the weak reading holds for every κ
--   - generalization: (d) increasing → also dΨ̃/dσ > 0 and StrictMonoOn on S(κ) when κ ≠ 1/2; reason: what (64) shows; the weak claim is stated for every κ
--   - reading: long-run ratings and prices of Proposition 1 → functions Ψ̃, p̃ of σ satisfying IsLongRunOutcome on S(κ), asserted to exist, with the signs for every such pair; reason: the stationary equilibrium to which the market converges from every rating (p.14)
--   - reading: (19) ψ̄_t = (1 − σ)ψ̄_t + σψ(p_t, ψ̄_t), with ψ̄_t on both sides → ratingPath with ψ̄_{t+1} on the left, from ψ̄_0 at t = 0; reason: the printed left side is an index slip: (3) and (22) have ψ̄_{t+1}; Appendix A's initial rating ψ̄₁ is the ψ̄₀ of (20)
--   - reading: max over (p_t)_{t≥0} of Σ δ^t p_t q(p_t, ψ̄_t) (18) → IsOptimalPlan: the plan's discounted series converges to V and every real plan's partial sums are eventually ≤ V + ε for every ε > 0; reason: the strongest natural reading of the maximum over all real price sequences, including those whose series does not converge
--   - reading: the linear-quadratic model: q = 2(ψ̄ − p(1−κ)) (7) and the review (9), with no boundary solutions specified (footnote 5) → demand, cutoff and review are the paper's affine formulas on all of ℝ², prices are arbitrary reals, nothing is clamped to [0,1]; reason: the paper solves exactly this unconstrained problem (its remarks that flow profits are bounded, pp.12 and 24, do not hold for these formulas and are not used); with clamping the value function is not quadratic and (28)–(29) are not derived
--   - generalization: σ ∈ [σ̄, 1] for a fixed σ̄ > 0 → every σ ∈ (0, 1] in the admissible set; reason: σ̄ is an arbitrary positive lower bound (p.6), so every σ the paper allows is covered
--   - encoding: d/dσ of the long-run quantities → HasDerivWithinAt on S(κ) with the stated sign; reason: the ordinary derivative at interior points; one-sided at σ = 1, the only boundary point of S(κ) that belongs to it
-- source:
--   Stenzel–Wolf–Schmidt, Pricing for the Stars: Dynamic Pricing in the Presence of Rating Systems, CRC TR 224 DP No. 143 (Jan 2020), Corollary 1, pp.14–15 (PDF 16–17); proof p.26 (PDF 28)

import Mathlib
import Definitions.Def_PricingStars_Model

namespace PricingStars

/-- Corollary 1 (Stenzel–Wolf–Schmidt, Pricing for the Stars, CRC TR 224 DP No. 143 (Jan 2020),
pp.14–15 (PDF 16–17); proof p.26 (PDF 28)). Fix a seller of type `θ > −1`, `δ ∈ (0,1)` and
`κ ∈ [0,1)`. The long-run rating and price exist as functions `Ψ̃(σ)`, `p̃(σ)` of the sensitivity
`σ` on the admissible set `S(κ)`, and for every such pair, at every `σ ∈ S(κ)` (derivatives within
`S(κ)`):
(a) `dp̃/dσ > 0` when `κ < 1/2` and `dp̃/dσ < 0` when `κ > 1/2`;
(b) `dC̃S/dσ < 0` when `κ < 1/2` and `dC̃S/dσ > 0` when `κ > 1/2`, where `C̃S(σ)` is the long-run
    consumer surplus at `(Ψ̃(σ), p̃(σ))`;
(c) `dπ̃/dσ > 0` when `κ ≠ 1/2`, where `π̃(σ) = p̃ · q(Ψ̃, p̃)`;
(d) `Ψ̃` is increasing on `S(κ)`, with `dΨ̃/dσ > 0` and strictly increasing when `κ ≠ 1/2`.

**Formalization Note** The long-run objects are the limits along the optimal plans of the seller's
problem (`IsLongRunOutcome`), never the closed forms (28)–(29). "Otherwise" in (a)–(b) is read as
`κ > 1/2`: at `κ = 1/2` the long-run rating, price and surplus do not depend on `σ`. The point
`(κ, σ) = (1/2, 1)`, where no long-run limit exists, is outside `S(κ)`. At `σ = 1` (for
`κ < 1/2`) the derivative is one-sided. -/
theorem corollary_1 (θ δ κ : ℝ) (hθ : -1 < θ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hκ0 : 0 ≤ κ)
    (hκ1 : κ < 1) :
    (∃ Ψf pf : ℝ → ℝ, ∀ σ ∈ admissibleSet κ, IsLongRunOutcome θ δ κ σ (Ψf σ) (pf σ)) ∧
    ∀ Ψf pf : ℝ → ℝ, (∀ σ ∈ admissibleSet κ, IsLongRunOutcome θ δ κ σ (Ψf σ) (pf σ)) →
      (∀ σ ∈ admissibleSet κ,
        (κ < 1 / 2 → ∃ D, HasDerivWithinAt pf D (admissibleSet κ) σ ∧ 0 < D) ∧
        (1 / 2 < κ → ∃ D, HasDerivWithinAt pf D (admissibleSet κ) σ ∧ D < 0) ∧
        (κ < 1 / 2 → ∃ D, HasDerivWithinAt (fun s => longRunCS θ κ (Ψf s) (pf s)) D
          (admissibleSet κ) σ ∧ D < 0) ∧
        (1 / 2 < κ → ∃ D, HasDerivWithinAt (fun s => longRunCS θ κ (Ψf s) (pf s)) D
          (admissibleSet κ) σ ∧ 0 < D) ∧
        (κ ≠ 1 / 2 → ∃ D, HasDerivWithinAt (fun s => longRunProfit κ (Ψf s) (pf s)) D
          (admissibleSet κ) σ ∧ 0 < D) ∧
        (κ ≠ 1 / 2 → ∃ D, HasDerivWithinAt Ψf D (admissibleSet κ) σ ∧ 0 < D)) ∧
      MonotoneOn Ψf (admissibleSet κ) ∧
      (κ ≠ 1 / 2 → StrictMonoOn Ψf (admissibleSet κ)) := by sorry

end PricingStars
