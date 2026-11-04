-- Prove2me | Theorems.Thm_PricingStars_proposition_1
-- name    : PricingStars.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:30:14.774333+00:00
-- url     : https://prove2.me/theorems/c51b144f-6c98-46bd-9816-9e43545f2ec6
-- title:
--   Proposition 1 — the unique stationary equilibrium $\tilde\Psi$ (28), $\tilde p$ (29), $\tilde\mu=\theta$ (30) (corrected: $(\kappa,\sigma)\neq(1/2,1)$)
-- statement:
--   Let $\theta>-1$, $\delta\in(0,1)$, $\kappa\in[0,1)$ and $\sigma\in S(\kappa)$, and put
--   $$
--   \tilde\Psi=\frac{(\theta+1)\bigl(2(1-\delta)(1-\kappa)+\delta\sigma(3-2\kappa)\bigr)}{4\delta\sigma+(1-\delta)(3-2\kappa)}\quad(28),\qquad
--   \tilde p=\frac{(\theta+1)\bigl((1-\delta)+2\delta\sigma\bigr)}{4\delta\sigma+(1-\delta)(3-2\kappa)}\quad(29).
--   $$
--   Then there is a unique stationary equilibrium, characterized by $\tilde\Psi$, $\tilde p$ and $\tilde\mu=\theta$ (30):
--
--   1. $(\tilde\Psi,\tilde p)$ is the long-run outcome: an optimal plan exists from every initial rating, and along every optimal plan the ratings converge to $\tilde\Psi$ and the prices to $\tilde p$;
--   2. from every initial rating the optimal plan is unique;
--   3. along every optimal plan, the consumers' inferred quality at $(\bar\psi_t,p_t)$ converges to $\theta$ — the rating system is effective and consumers learn the quality;
--   4. from $\bar\psi_0=\tilde\Psi$ the constant plan $\tilde p$ is optimal and keeps the rating at $\tilde\Psi$, and the inference at $(\tilde\Psi,\tilde p)$ has quality $\theta$.
--
--   This identifies the long-run rating and price on which the comparative statics of Corollary 1 are computed.
--
--   Differences from the source:
--   - correction: technical assumption: σ < 1 − κ only when κ > 1/2 (p.7), so (κ, σ) = (1/2, 1) is allowed; footnote 12 claims κ < max{1/2, 1 − σ} holds → the admissible set also excludes the single point (κ, σ) = (1/2, 1); reason: there the price does not move the review and ψ̄' = θ + 1 − ψ̄; at θ = 0, δ = 1/2, ψ̄₀ = 0 the unique optimal plan is myopic and the ratings run 0, 1, 0, 1, …, so no long-run limit exists and b = −1
--   - reading: 'there is a unique stationary equilibrium … to which the market converges' characterized by (28)–(30) → clauses 1–4: long-run outcome, unique optimal plan from every ψ̄₀, inferred quality → θ along every optimal plan, and stationarity at Ψ̃; reason: p.14 describes the equilibrium as the unique steady state to which the market converges from every rating
--   - reading: (19) ψ̄_t = (1 − σ)ψ̄_t + σψ(p_t, ψ̄_t), with ψ̄_t on both sides → ratingPath with ψ̄_{t+1} on the left, from ψ̄_0 at t = 0; reason: the printed left side is an index slip: (3) and (22) have ψ̄_{t+1}; Appendix A's initial rating ψ̄₁ is the ψ̄₀ of (20)
--   - reading: max over (p_t)_{t≥0} of Σ δ^t p_t q(p_t, ψ̄_t) (18) → IsOptimalPlan: the plan's discounted series converges to V and every real plan's partial sums are eventually ≤ V + ε for every ε > 0; reason: the strongest natural reading of the maximum over all real price sequences, including those whose series does not converge
--   - reading: the linear-quadratic model: q = 2(ψ̄ − p(1−κ)) (7) and the review (9), with no boundary solutions specified (footnote 5) → demand, cutoff and review are the paper's affine formulas on all of ℝ², prices are arbitrary reals, nothing is clamped to [0,1]; reason: the paper solves exactly this unconstrained problem (its remarks that flow profits are bounded, pp.12 and 24, do not hold for these formulas and are not used); with clamping the value function is not quadratic and (28)–(29) are not derived
--   - generalization: σ ∈ [σ̄, 1] for a fixed σ̄ > 0 → every σ ∈ (0, 1] in the admissible set; reason: σ̄ is an arbitrary positive lower bound (p.6), so every σ the paper allows is covered
-- source:
--   Stenzel–Wolf–Schmidt, Pricing for the Stars: Dynamic Pricing in the Presence of Rating Systems, CRC TR 224 DP No. 143 (Jan 2020), Proposition 1, p.14 (PDF 16); proof Appendix A, pp.24–26 (PDF 26–28)

import Mathlib
import Definitions.Def_PricingStars_Model

open Filter Topology

namespace PricingStars

/-- Proposition 1 (Stenzel–Wolf–Schmidt, Pricing for the Stars, CRC TR 224 DP No. 143 (Jan 2020),
p.14 (PDF 16); proof Appendix A, pp.24–26 (PDF 26–28)). For a seller of type `θ > −1`, `δ ∈ (0,1)`,
`κ ∈ [0,1)` and `σ` in the admissible set, let `Ψ̃` be (28) and `p̃` be (29). Then there is a unique
stationary equilibrium characterized by `Ψ̃`, `p̃` and `μ̃ = θ` (30):
1. `(Ψ̃, p̃)` is the long-run outcome: from every initial rating an optimal plan exists, and along
   every optimal plan the ratings converge to `Ψ̃` and the prices to `p̃`;
2. from every initial rating the optimal plan is unique;
3. along every optimal plan, every sequence of consumer inferences `(μ_t, ω_t)` at `(ψ̄_t, p_t)` has
   inferred quality `μ_t → θ` (consumers learn the quality);
4. from `ψ̄₀ = Ψ̃` the constant plan `p̃` is optimal and keeps the rating at `Ψ̃`, and the inferred
   quality at `(Ψ̃, p̃)` is `θ`.

**Formalization Note** The point `(κ, σ) = (1/2, 1)` is excluded by the admissible set: there
(`θ = 0`, `δ = 1/2`, `ψ̄₀ = 0`) the optimal plan is myopic and the ratings run `0, 1, 0, 1, …`.
The denominator `4δσ + (1 − δ)(3 − 2κ)` is positive. The model is the paper's unclamped
linear-quadratic one, and optimality is `IsOptimalPlan`. -/
theorem proposition_1 (θ δ κ σ : ℝ) (hθ : -1 < θ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hκ0 : 0 ≤ κ)
    (hκ1 : κ < 1) (hσ : σ ∈ admissibleSet κ) :
    let Ψ := (θ + 1) * (2 * (1 - δ) * (1 - κ) + δ * σ * (3 - 2 * κ)) /
      (4 * δ * σ + (1 - δ) * (3 - 2 * κ))
    let p := (θ + 1) * ((1 - δ) + 2 * δ * σ) / (4 * δ * σ + (1 - δ) * (3 - 2 * κ))
    IsLongRunOutcome θ δ κ σ Ψ p ∧
    (∀ ψ₀ : ℝ, ∃! plan : ℕ → ℝ, IsOptimalPlan θ δ κ σ ψ₀ plan) ∧
    (∀ (ψ₀ : ℝ) (plan : ℕ → ℝ) (μ ω : ℕ → ℝ), IsOptimalPlan θ δ κ σ ψ₀ plan →
      (∀ t, IsInference κ (ratingPath θ κ σ ψ₀ plan t) (plan t) (μ t) (ω t)) →
      Tendsto μ atTop (𝓝 θ)) ∧
    (IsOptimalPlan θ δ κ σ Ψ (fun _ => p) ∧ (∀ t, ratingPath θ κ σ Ψ (fun _ => p) t = Ψ) ∧
      ∀ μ ω : ℝ, IsInference κ Ψ p μ ω → μ = θ) := by sorry

end PricingStars
