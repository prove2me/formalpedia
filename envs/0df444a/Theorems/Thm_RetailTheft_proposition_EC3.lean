-- Prove2me | Theorems.Thm_RetailTheft_proposition_EC3
-- name    : RetailTheft.proposition_EC3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:14:08.235977+00:00
-- url     : https://prove2.me/theorems/5990e78c-a521-4fde-bb51-42e67e3de241
-- title:
--   Proposition EC.3 — the optimal price $p^*$ under uniform demand, and $\lambda_1\le\lambda_2$
-- statement:
--   Let demand be $D_p=a p^{-b}\varepsilon$ with $\varepsilon$ uniform on $[1-\alpha,1+\alpha]$, $a>0$, $b>1$, $c>0$, $0<\alpha\le1$, and let $\theta,\lambda\in[0,1)$. Let $p^*$ be the price of the four scenarios split at $\lambda_1$, $\lambda_2$ and $\theta/(1+\theta)$ (see the definition `RetailTheft.Uniform`). Then:
--
--   1. $p^*>0$ and $p^*$ is the unique maximizer of $V$ over $p>0$: $V(p)<V(p^*)$ for every $p>0$, $p\ne p^*$;
--   2. with both ex ante and ex post diversion, an optimal contract of problem (5)–(7) is $(q^*,R_{\bar r^*},p^*)$: there is $\bar r^*\in[0,p^*q^*]$ such that $(p^*,q^*,R_{\bar r^*},q^*,\mathrm{id})$ is an optimal tuple, where $q^*$ is the capacity of Proposition 1 at the price $p^*$;
--   3. $\lambda_1\le\lambda_2$.
--
--   The four scenarios are the backbone of the comparative statics of Theorem 2: constant price, then $\theta c/\lambda$, then the interior optimum of the second branch of (13), then the fixed-percentage regime.
--
--   Differences from the source:
--   - reading: "For the optimal price: … we have the optimal price p* = …" → p* > 0 and p* is the unique maximizer of V over p > 0; reason: "the optimal price" presupposes uniqueness; V is the fixed-price value of (5) (Corollary 1, with its corrected θcq̃)
--   - reading: "an optimal contract is (q*, R_r̄*, p) where the optimal capacity and repayment function are provided in Proposition 1" → some r̄ ∈ [0, p*q*] makes (p*, q*, R_r̄, q*, id) an optimal tuple of (5)–(7), with q* the capacity of Proposition 1 at p*; reason: the existence reading of "an optimal contract"
--   - encoding: λ < θ/(1+θ), λ ≥ θ/(1+θ), and the branch conditions of V and of q* in Proposition 1 → λ(1+θ) < θ, θ ≤ λ(1+θ), and those conditions multiplied out; reason: multiplied out by positive quantities; same instances, no division by λ
--   - reading: footnote 1: among the agent's best responses, the one that maximizes the principal's utility → optimality is joint maximization over (p, q, R, q′, γ) subject to (q′, γ) being a best response; reason: this is exactly the principal-favourable tie-breaking of footnote 1
--   - reading: ε uniform on [1 − α, 1 + α] for some α ≤ 1 → 0 < α ≤ 1, law (2α)⁻¹·Lebesgue on [1 − α, 1 + α]; reason: at α = 0 the law is a point mass and F̄_p^{-1} is not a root; the paper's displays divide by α
--   - reading: a ∈ ℝ₊, c a unit cost, θ < 1, λ < 1 → a > 0, c > 0, 0 ≤ θ < 1, 0 ≤ λ < 1; reason: degenerate cases excluded; efficiencies are nonnegative and Theorem 2 fixes θ ∈ [0,1)
--   - reading: p ∈ ℝ₊ → p > 0; reason: demand a p^{-b} ε is undefined at p = 0
--   - reading: F̄_p^{-1}, the inverse of F̄_p → the largest q ≥ 0 with F̄_p(q) ≥ y; reason: the unique root of F̄_p(q) = y for y ∈ (0,1); at y = 1 the bottom of the support
--   - reading: Γ = all γ with γ(r) ≤ r for r ≥ 0 → measurable γ with 0 ≤ γ(r) ≤ r for r ≥ 0; reason: the expectation in (4) presupposes measurability, and R is only defined on reports r ≥ 0
--   - encoding: R nondecreasing on [0,∞) with R(r) ≤ r → R Monotone on ℝ with R(r) ≤ r for r ≥ 0; reason: only values on [0,∞) are evaluated; every R nondecreasing on [0,∞) agrees there with the monotone r ↦ R(max r 0)
-- source:
--   Chen–Tian–Zuo, Optimal Capacity and Price Designs Under Ex Ante and Ex Post Theft, MSOM (2025), doi:10.1287/msom.2025.0024, e-companion, Proposition EC.3, pp. ec9–ec10 (PDF 42–43); proof pp. ec11–ec12

import Mathlib
import Definitions.Def_RetailTheft_Model
import Definitions.Def_RetailTheft_Uniform

open MeasureTheory

namespace RetailTheft

/-- **Proposition EC.3** of Chen, Tian and Zuo, *Optimal Capacity and Price Designs Under Ex Ante
and Ex Post Theft*, MSOM (2025), doi:10.1287/msom.2025.0024, e-companion, pp. ec9–ec10
(PDF 42–43); proof pp. ec11–ec12. Uniform demand `ε ~ U[1 − α, 1 + α]`, `0 < α ≤ 1`. With both
ex ante and ex post diversion, an optimal contract is `(q*, R_r̄*, p*)`, where the optimal
capacity and repayment function are those of Proposition 1 and the optimal price `p*` is
`priceStar` (four scenarios, split at `λ₁`, `λ₂`, `θ/(1+θ)`); moreover `λ₁ ≤ λ₂`. Precisely:
1. `p* > 0` and `p*` is the unique maximizer of `V` over `p > 0`;
2. for some `r̄ ∈ [0, p*q*]`, `(p*, q*, R_r̄, q*, id)` is an optimal tuple of (5)–(7), where
   `q* = capStar` is the capacity of Proposition 1 at the price `p*`;
3. `λ₁ ≤ λ₂`.

**Formalization Note** "The optimal price" is read as the unique maximizer of `V` (the value of
problem (5) at a fixed price, Corollary 1). `λ < θ/(1+θ)` is written `λ(1+θ) < θ`. -/
theorem proposition_EC3 (a b c α θ lam : ℝ) (ha : 0 < a) (hb : 1 < b) (hc : 0 < c)
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hlam0 : 0 ≤ lam)
    (hlam1 : lam < 1) :
    0 < priceStar b c α θ lam ∧
    (∀ p : ℝ, 0 < p → p ≠ priceStar b c α θ lam →
      V (uniformModel a b c α) θ lam p < V (uniformModel a b c α) θ lam (priceStar b c α θ lam)) ∧
    (∃ rbar, 0 ≤ rbar ∧
      rbar ≤ priceStar b c α θ lam *
        capStar (uniformModel a b c α) θ lam (priceStar b c α θ lam) ∧
      IsOptimal (uniformModel a b c α) θ lam (priceStar b c α θ lam)
        (capStar (uniformModel a b c α) θ lam (priceStar b c α θ lam)) (thresholdR lam rbar)
        (capStar (uniformModel a b c α) θ lam (priceStar b c α θ lam)) id) ∧
    lam1 b α θ ≤ lam2 b α θ := by sorry

end RetailTheft
