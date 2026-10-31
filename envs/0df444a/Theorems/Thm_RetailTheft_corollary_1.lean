-- Prove2me | Theorems.Thm_RetailTheft_corollary_1
-- name    : RetailTheft.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:13:15.303831+00:00
-- url     : https://prove2.me/theorems/8b6a9065-5ed7-4b13-9ab4-98eee8924ad9
-- title:
--   Corollary 1 (corrected: $\theta c\tilde q$) — problem (5) reduces to $\max_p V(p)$
-- statement:
--   Consider the retail-theft model with the standing assumptions and $\theta,\lambda\in[0,1)$. For every price $p>0$, the optimal value of the principal's problem (5)–(7) among feasible tuples with price $p$ is attained and equals $V(p)$, where, with $q^*$ and $\tilde q$ as in Proposition 1:
--
--   - when $\lambda<\theta/(1+\theta)$,
--   $$
--   V(p)=\begin{cases}\mathbb E[P_{p,q^*}]-(1+\theta)cq^*, & (1+\theta)c<p\le\theta c/\lambda,\\ \mathbb E[P_{p,q^*}]-\lambda\mathbb E[P_{p,\tilde q}]-(1+\theta)cq^*+\theta c\tilde q, & p>\theta c/\lambda,\\ 0, & \text{otherwise;}\end{cases}\qquad(13)
--   $$
--   - when $\lambda\ge\theta/(1+\theta)$,
--   $$
--   V(p)=\begin{cases}(1-\lambda)\mathbb E[P_{p,q^*}]-cq^*, & p>c/(1-\lambda),\\ 0, & \text{otherwise.}\end{cases}\qquad(14)
--   $$
--
--   Hence problem (5) is the pricing problem $\max_{p>0}V(p)$ (12), the foundation of the comparative statics in the price and capacity.
--
--   Differences from the source:
--   - correction: second branch of (13): … − (1+θ)cq* + θq̃ → … − (1+θ)cq* + θcq̃; reason: the proof of Proposition EC.2 ((EC.21), p. ec8) gives the principal's utility E[P_{p,q*}] − λE[P_{p,q̃}] − (1+θ)cq* + θcq̃; the printed value differs from it by θ(c−1)q̃ ≠ 0 whenever c ≠ 1 (q̃ > 0 in that branch), e.g. uniform α = 1/2, a = 1, b = 2, c = 2, θ = 0.7, λ = 0.3, p = 5
--   - reading: "problem (5) can be reformulated as max_{p∈ℝ₊} V(p)" → for every p > 0, V(p) is the greatest objective value among feasible tuples of (5)–(7) with price p; reason: the reformulation holds price by price
--   - encoding: p ≤ θc/λ, p > θc/λ, p > c/(1−λ), λ < θ/(1+θ) → λp ≤ θc, θc < λp, c < (1−λ)p, λ(1+θ) < θ; reason: multiplied out; at λ = 0, λp ≤ θc is the paper's p ≤ θc/0 = +∞
--   - reading: footnote 1: among the agent's best responses, the one that maximizes the principal's utility → optimality is joint maximization over (p, q, R, q′, γ) subject to (q′, γ) being a best response; reason: this is exactly the principal-favourable tie-breaking of footnote 1
--   - reading: p ∈ ℝ₊ (p ≥ 0 in (8)) → p > 0; reason: demand a p^{-b} ε is undefined at p = 0, and Proposition 1 fixes p > 0
--   - reading: F̄_p^{-1}, the inverse of F̄_p → the largest q ≥ 0 with F̄_p(q) ≥ y; reason: the unique root of F̄_p(q) = y for y ∈ (0,1), the only inputs V uses
--   - reading: ε nonnegative with a known distribution and a well-defined inverse function; a ∈ ℝ₊; c a unit cost → μ a probability measure with μ(−∞,0) = 0 whose cdf is continuous and strictly increasing where 0 < F < 1; a > 0; c > 0; reason: the standard reading of a continuous, invertible demand law; a = 0 or c = 0 is degenerate
--   - reading: θ < 1, λ < 1 → 0 ≤ θ < 1, 0 ≤ λ < 1; reason: stealing efficiencies are nonnegative (the agent earns θc per stolen unit, λ per stolen dollar); Theorems 1–2 fix θ, λ ∈ [0,1)
--   - reading: Γ = all γ with γ(r) ≤ r for r ≥ 0 → measurable γ with 0 ≤ γ(r) ≤ r for r ≥ 0; reason: the expectation in (4) presupposes measurability, and R is only defined on reports r ≥ 0
--   - encoding: R nondecreasing on [0,∞) with R(r) ≤ r → R Monotone on ℝ with R(r) ≤ r for r ≥ 0; reason: only values on [0,∞) are evaluated; every R nondecreasing on [0,∞) agrees there with the monotone r ↦ R(max r 0)
-- source:
--   Chen–Tian–Zuo, Optimal Capacity and Price Designs Under Ex Ante and Ex Post Theft, MSOM (2025), doi:10.1287/msom.2025.0024, Corollary 1, pp. 14–15 (PDF 14–15); corrected term from the proof of Proposition EC.2, p. ec8

import Mathlib
import Definitions.Def_RetailTheft_Model

open MeasureTheory

namespace RetailTheft

/-- **Corollary 1** (corrected: `θcq̃` for `θq̃`) of Chen, Tian and Zuo, *Optimal Capacity and
Price Designs Under Ex Ante and Ex Post Theft*, MSOM (2025), doi:10.1287/msom.2025.0024,
pp. 14–15 (PDF 14–15). The principal's problem (5) can be reformulated as `max_{p ∈ ℝ₊} V(p)`
(12), with `V` given by (13)–(14): for every price `p > 0`, the optimal value of (5)–(7) among
feasible tuples with price `p` is attained and equals `V(p)`.

**Formalization Note** `V` is `RetailTheft.V`, whose second branch of (13) carries the
corrected term `+ θcq̃` (the printed `+ θq̃` is off by `θ(c − 1)q̃`; see the proof of Proposition
EC.2, p. ec8). "Can be reformulated as" is stated as `IsGreatest` of the set of fixed-price
objective values. -/
theorem corollary_1 (M : Params) (hM : M.Standing) (θ lam : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (p : ℝ) (hp : 0 < p) :
    IsGreatest {v : ℝ | ∃ (q : ℝ) (R : ℝ → ℝ) (q' : ℝ) (γ : ℝ → ℝ),
      IsFeasible M θ lam p q R q' γ ∧ v = objective M p q R q' γ} (V M θ lam p) := by sorry

end RetailTheft
