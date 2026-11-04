-- Prove2me | Theorems.Thm_PricingStars_optimal_policy_linear
-- name    : PricingStars.optimal_policy_linear
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:30:19.151606+00:00
-- url     : https://prove2.me/theorems/793e7a40-ac63-4408-9835-d5c5315db3a2
-- title:
--   Appendix A, (56)–(58) — quadratic value, unique optimal plan, linear law of motion $\bar\psi'=a+b\bar\psi$ with $|b|<1$ (corrected: $(\kappa,\sigma)\neq(1/2,1)$)
-- statement:
--   Let $\delta\in(0,1)$, $\kappa\in[0,1)$, $\sigma\in S(\kappa)$ and any quality $\theta$. Put
--   $$
--   r=\sqrt{\bigl(\delta(1-2\sigma)^2-1\bigr)\bigl(\delta(\kappa+\sigma-1)^2-(\kappa-1)^2\bigr)},
--   $$
--   $$
--   a=\frac{\sigma(\theta+1)\bigl(\delta(3-2\kappa)\sigma+2(1-\delta)(1-\kappa)\bigr)}{2\delta\sigma^2+(1-\kappa)(1-\delta)+r}\quad(57),\qquad
--   b=\frac{1-\kappa+\delta(2\sigma-1)(\kappa+\sigma-1)-r}{\delta\bigl(2(1-\kappa)-(3-2\kappa)\sigma\bigr)}\quad(58).
--   $$
--   Then:
--
--   1. $|b|<1$;
--   2. from every initial rating $\bar\psi_0$ the seller's problem (18)–(20) has exactly one optimal plan;
--   3. along every optimal plan the rating follows the law of motion (56), $\bar\psi_{t+1}=a+b\,\bar\psi_t$ for all $t$;
--   4. the value is quadratic: there are constants $c,d,e$ such that every optimal plan from $\bar\psi_0$ has discounted profit $c+d\bar\psi_0+e\bar\psi_0^2$.
--
--   This is the verification step behind Proposition 1: the stable linear policy and its fixed point $a/(1-b)$ give the long-run rating.
--
--   **Formalization Note** At $\sigma=2(1-\kappa)/(3-2\kappa)$ numerator and denominator of (58) both vanish and the true coefficient is $b=0$; Lean's convention $x/0=0$ returns exactly this value, so no hypothesis excludes that point. Appendix A's initial rating $\bar\psi_1$ is the $\bar\psi_0$ of (20).
--
--   Differences from the source:
--   - correction: technical assumption: σ < 1 − κ only when κ > 1/2 (p.7), so (κ, σ) = (1/2, 1) is allowed; footnote 12 claims κ < max{1/2, 1 − σ} holds → the admissible set also excludes the single point (κ, σ) = (1/2, 1); reason: there the price does not move the review and ψ̄' = θ + 1 − ψ̄; at θ = 0, δ = 1/2, ψ̄₀ = 0 the unique optimal plan is myopic and the ratings run 0, 1, 0, 1, …, so no long-run limit exists and b = −1
--   - encoding: (58) at σ = 2(1 − κ)/(3 − 2κ), where it reads 0/0 → Lean's x/0 = 0, which is the true b = 0 there; reason: (58) tends to 0 at that point and value iteration gives b = 0; no instance changes
--   - reading: 'the value function is of the form V(ψ̄) = c + dψ̄ + eψ̄²' and 'only one feasible optimal policy' → exactly one optimal plan from every ψ̄₀, whose value is c + dψ̄₀ + eψ̄₀²; reason: the paper's guess-and-verify conclusion and uniqueness paragraph (pp.13, 26), stated about the plans of (18)–(20)
--   - reading: (56) prints its second fraction without a factor ψ̄ → ψ̄_{t+1} = a + b ψ̄_t; reason: the next sentence after (58) says ψ̄′ = a + bψ̄, and (55) has the factor ψ̄; (56) dropped it
--   - reading: (19) ψ̄_t = (1 − σ)ψ̄_t + σψ(p_t, ψ̄_t), with ψ̄_t on both sides → ratingPath with ψ̄_{t+1} on the left, from ψ̄_0 at t = 0; reason: the printed left side is an index slip: (3) and (22) have ψ̄_{t+1}; Appendix A's initial rating ψ̄₁ is the ψ̄₀ of (20)
--   - reading: max over (p_t)_{t≥0} of Σ δ^t p_t q(p_t, ψ̄_t) (18) → IsOptimalPlan: the plan's discounted series converges to V and every real plan's partial sums are eventually ≤ V + ε for every ε > 0; reason: the strongest natural reading of the maximum over all real price sequences, including those whose series does not converge
--   - reading: the linear-quadratic model: q = 2(ψ̄ − p(1−κ)) (7) and the review (9), with no boundary solutions specified (footnote 5) → demand, cutoff and review are the paper's affine formulas on all of ℝ², prices are arbitrary reals, nothing is clamped to [0,1]; reason: the paper solves exactly this unconstrained problem (its remarks that flow profits are bounded, pp.12 and 24, do not hold for these formulas and are not used); with clamping the value function is not quadratic and (28)–(29) are not derived
--   - generalization: σ ∈ [σ̄, 1] for a fixed σ̄ > 0 → every σ ∈ (0, 1] in the admissible set; reason: σ̄ is an arbitrary positive lower bound (p.6), so every σ the paper allows is covered
--   - generalization: θ > −1 (Proposition 1, whose proof this is) → every real θ; reason: the derivation in Appendix A does not use the sign of θ + 1; the coefficients b and the Riccati recursion do not involve θ
-- source:
--   Stenzel–Wolf–Schmidt, Pricing for the Stars: Dynamic Pricing in the Presence of Rating Systems, CRC TR 224 DP No. 143 (Jan 2020), Appendix A, Derivation and Proof of Proposition 1, (56)–(58) and footnote 12, p.25 (PDF 27); |b| < 1 also p.15 (PDF 17); uniqueness p.26 (PDF 28)

import Mathlib
import Definitions.Def_PricingStars_Model

namespace PricingStars

/-- Appendix A, Derivation and Proof of Proposition 1, (56)–(58) and footnote 12 (Stenzel–Wolf–
Schmidt, Pricing for the Stars, CRC TR 224 DP No. 143 (Jan 2020), p.25 (PDF 27); `|b| < 1` also
p.15 (PDF 17)). For `δ ∈ (0,1)`, `κ ∈ [0,1)`, `σ` in the admissible set and any `θ`, let
`a` be (57) and `b` be (58). Then `|b| < 1`; from every initial rating the seller's problem
(18)–(20) has exactly one optimal plan; along it the rating follows the linear law of motion
`ψ̄' = a + bψ̄` (56); and the optimal value is quadratic in the initial rating,
`V(ψ̄₀) = c + dψ̄₀ + eψ̄₀²`.

**Formalization Note** At `σ = 2(1 − κ)/(3 − 2κ)` the numerator and denominator of (58) both
vanish and the true coefficient is `b = 0`; Lean's `x / 0 = 0` returns exactly that value, so no
hypothesis excludes the point. The point `(κ, σ) = (1/2, 1)` (where `b = −1`) is outside the
admissible set. Optimality is `IsOptimalPlan` (convergent value, limsup comparison with every real
plan); the model is the paper's unclamped linear-quadratic one; `θ` is unrestricted. -/
theorem optimal_policy_linear (θ δ κ σ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hκ0 : 0 ≤ κ)
    (hκ1 : κ < 1) (hσ : σ ∈ admissibleSet κ) :
    let r := Real.sqrt ((δ * (1 - 2 * σ) ^ 2 - 1) * (δ * (κ + σ - 1) ^ 2 - (κ - 1) ^ 2))
    let a := σ * (θ + 1) * (δ * (3 - 2 * κ) * σ + 2 * (1 - δ) * (1 - κ)) /
      (2 * δ * σ ^ 2 + (1 - κ) * (1 - δ) + r)
    let b := (1 - κ + δ * (2 * σ - 1) * (κ + σ - 1) - r) /
      (δ * (2 * (1 - κ) - (3 - 2 * κ) * σ))
    |b| < 1 ∧
    (∀ ψ₀ : ℝ, ∃! plan : ℕ → ℝ, IsOptimalPlan θ δ κ σ ψ₀ plan) ∧
    (∀ (ψ₀ : ℝ) (plan : ℕ → ℝ), IsOptimalPlan θ δ κ σ ψ₀ plan →
      ∀ t : ℕ, ratingPath θ κ σ ψ₀ plan (t + 1) = a + b * ratingPath θ κ σ ψ₀ plan t) ∧
    ∃ c d e : ℝ, ∀ (ψ₀ : ℝ) (plan : ℕ → ℝ), IsOptimalPlan θ δ κ σ ψ₀ plan →
      HasSum (discProfit θ δ κ σ ψ₀ plan) (c + d * ψ₀ + e * ψ₀ ^ 2) := by sorry

end PricingStars
