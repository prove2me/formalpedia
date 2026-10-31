-- Prove2me | Theorems.Thm_RetailTheft_proposition_1
-- name    : RetailTheft.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:13:18.519706+00:00
-- url     : https://prove2.me/theorems/3c5b3ed8-5973-4bde-ba11-30b6e02f1c01
-- title:
--   Proposition 1 — optimal capacity $q^*$ and threshold $\bar r^*$ at a fixed price
-- statement:
--   Consider the retail-theft model with the standing assumptions and $\theta,\lambda\in[0,1)$. Fix a price $p>0$. Then problem (5) at price $p$ has a feasible tuple, and an optimal contract $(q^*,R_{\bar r^*},p)$ — optimal among all feasible tuples of (5)–(7) with price $p$, with no stealing — is as follows. Write $q_1^*=\bar F_p^{-1}((1+\theta)c/p)$.
--
--   1. If $\lambda\le\theta c/p$ and $p>(1+\theta)c$: $q^*=q_1^*$, and $0\le\bar r^*\le pq^*$ with
--   $$\mathbb E[P_{p,q^*}-R_{\bar r^*}(P_{p,q^*})]=\theta cq^*.\qquad(10)$$
--   2. If $\theta c/p<\lambda<\theta/(1+\theta)$: $q^*=q_1^*$, and $0\le\bar r^*\le pq^*$ with
--   $$\mathbb E[P_{p,q^*}-R_{\bar r^*}(P_{p,q^*})]=\lambda\mathbb E[P_{p,\tilde q}]+\theta c(q^*-\tilde q)>\theta cq^*,\qquad(11)$$
--   where $\tilde q=\bar F_p^{-1}(\theta c/(\lambda p))$.
--   3. If $\lambda\ge\theta/(1+\theta)$ and $p\ge c/(1-\lambda)$: $q^*=\bar F_p^{-1}(c/((1-\lambda)p))$ and $\bar r^*=pq^*$; equivalently, the fixed-percentage commission $R(r)=(1-\lambda)r$ is optimal at $q^*$.
--   4. Otherwise production is abandoned: $q^*=0$.
--
--   Moreover, in cases 1 and 2 the threshold strictly increases with $\lambda$ (price and all other data fixed): if $\lambda_1<\lambda_2$ both lie in case 1 (resp. case 2) and $\bar r_1,\bar r_2\in[0,pq^*]$ satisfy (10) (resp. (11)) at $\lambda_1$ and $\lambda_2$, then $\bar r_1<\bar r_2$.
--
--   This reduces the principal's problem to a one-dimensional problem in the price, and shows how the stealing efficiencies shape the commission.
--
--   Differences from the source:
--   - reading: "the revenue threshold r̄* increases with λ" → strictly increases: λ₁ < λ₂ in the same case and r̄₁, r̄₂ ∈ [0,pq*] solving (10) (resp. (11)) give r̄₁ < r̄₂; reason: the paper distinguishes "strictly" and "weakly" elsewhere; the stronger reading is taken (it holds: E[(r̄ ∧ P)] is strictly increasing on [0,pq*])
--   - reading: "the optimal capacity decision is q*" and "an optimal contract (q*, R_r̄*, p)" → there is a fixed-price optimal tuple (p, q*, R_r̄*, q*, id) of (5)–(7); reason: at p = c/(1−λ) in case (3) the optimal capacity is not unique; the existence reading is the printed claim
--   - reading: "R_r̄* has a revenue threshold r̄* = pq*, or equivalently, R_r̄*(r) = (1 − λ)r for all r ≥ 0" → r̄* = pq*, and (p, q*, r ↦ (1 − λ)r, q*, id) is also a fixed-price optimal tuple; reason: R_r̄* with r̄* = pq* equals (1 − λ)r only on r ≤ pq*, so the printed equality for all r ≥ 0 is read as optimality of the linear commission; the two agree on every report
--   - reading: F̄_p^{-1}, the inverse of F̄_p → the largest q ≥ 0 with F̄_p(q) ≥ y; reason: the unique root of F̄_p(q) = y for y ∈ (0,1); at y = 1 (case (3) with p = c/(1−λ)) the bottom of the support
--   - encoding: λ ≤ θc/p, θc/p < λ, λ < θ/(1+θ), λ ≥ θ/(1+θ), p ≥ c/(1−λ) → λp ≤ θc, θc < λp, λ(1+θ) < θ, θ ≤ λ(1+θ), c ≤ (1−λ)p; reason: the conditions multiplied out by positive quantities; same instances, no division by λ
--   - reading: "fix price p > 0 … an optimal contract" → optimal among feasible tuples of (5)–(7) with the same price p; reason: the price is held fixed
--   - reading: footnote 1: among the agent's best responses, the one that maximizes the principal's utility → optimality is joint maximization over (p, q, R, q′, γ) subject to (q′, γ) being a best response; reason: this is exactly the principal-favourable tie-breaking of footnote 1
--   - reading: ε nonnegative with a known distribution and a well-defined inverse function; a ∈ ℝ₊; c a unit cost → μ a probability measure with μ(−∞,0) = 0 whose cdf is continuous and strictly increasing where 0 < F < 1; a > 0; c > 0; reason: the standard reading of a continuous, invertible demand law; a = 0 or c = 0 is degenerate
--   - reading: θ < 1, λ < 1 → 0 ≤ θ < 1, 0 ≤ λ < 1; reason: stealing efficiencies are nonnegative (the agent earns θc per stolen unit, λ per stolen dollar); Theorems 1–2 fix θ, λ ∈ [0,1)
--   - reading: Γ = all γ with γ(r) ≤ r for r ≥ 0 → measurable γ with 0 ≤ γ(r) ≤ r for r ≥ 0; reason: the expectation in (4) presupposes measurability, and R is only defined on reports r ≥ 0
--   - encoding: R nondecreasing on [0,∞) with R(r) ≤ r → R Monotone on ℝ with R(r) ≤ r for r ≥ 0; reason: only values on [0,∞) are evaluated; every R nondecreasing on [0,∞) agrees there with the monotone r ↦ R(max r 0)
-- source:
--   Chen–Tian–Zuo, Optimal Capacity and Price Designs Under Ex Ante and Ex Post Theft, MSOM (2025), doi:10.1287/msom.2025.0024, Proposition 1, p. 13 (PDF 13); proof pp. ec6–ec9 (Propositions EC.1, EC.2)

import Mathlib
import Definitions.Def_RetailTheft_Model

open MeasureTheory

namespace RetailTheft

/-- **Proposition 1** of Chen, Tian and Zuo, *Optimal Capacity and Price Designs Under Ex Ante
and Ex Post Theft*, MSOM (2025), doi:10.1287/msom.2025.0024, p. 13 (PDF 13); proof pp. ec6–ec9.
Fix a price `p > 0`. The principal's problem (5) at `p` is feasible, and an optimal contract
`(q*, R_r̄*, p)` (optimal among all feasible tuples of (5)–(7) with price `p`, with no stealing)
is as follows, where `q*₁ = F̄_p^{-1}((1+θ)c/p)`:
1. if `λ ≤ θc/p` and `p > (1+θ)c`: `q* = q*₁`, and `r̄* ≤ pq*` satisfies (10)
   `E[P_{p,q*} − R_r̄*(P_{p,q*})] = θcq*`;
2. if `θc/p < λ < θ/(1+θ)`: `q* = q*₁`, and `r̄* ≤ pq*` satisfies (11)
   `E[P_{p,q*} − R_r̄*(P_{p,q*})] = λE[P_{p,q̃}] + θc(q* − q̃) > θcq*`, `q̃ = F̄_p^{-1}(θc/(λp))`;
3. if `λ ≥ θ/(1+θ)` and `p ≥ c/(1−λ)`: `q* = F̄_p^{-1}(c/((1−λ)p))` and `r̄* = pq*`, or
   equivalently the linear commission `R(r) = (1−λ)r` is optimal at `q*`;
4. otherwise `q* = 0`.
Furthermore, in cases (1) and (2) the threshold `r̄*` strictly increases with `λ` (the price `p`
and all other data held fixed): if `λ₁ < λ₂` both lie in case (1) (resp. (2)) and
`r̄₁, r̄₂ ∈ [0, pq*]` satisfy (10) (resp. (11)) at `λ₁` and `λ₂`, then `r̄₁ < r̄₂`.

**Formalization Note** Branch conditions are multiplied out: `λp ≤ θc`, `θc < λp`,
`λ(1+θ) < θ`, `θ ≤ λ(1+θ)`, `c ≤ (1−λ)p`. "Increases" is read as strictly increases. "The
optimal capacity decision is `q*`" is stated as the existence of a fixed-price optimal tuple with
capacity `q*` and no stealing (`q' = q*`, `γ = id`); at `p = c/(1−λ)` in case (3) the optimal
capacity is not unique. The printed "`R_r̄*(r) = (1−λ)r` for all `r ≥ 0`" holds for `R_r̄*` only on
`r ≤ pq*`, so in case (3) the linear commission is stated as a second optimal tuple. -/
theorem proposition_1 (M : Params) (hM : M.Standing) (θ lam : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (p : ℝ) (hp : 0 < p) :
    (∃ (q : ℝ) (R : ℝ → ℝ) (q' : ℝ) (γ : ℝ → ℝ), IsFeasible M θ lam p q R q' γ) ∧
    (lam * p ≤ θ * M.c → (1 + θ) * M.c < p →
      ∃ rbar, 0 ≤ rbar ∧ rbar ≤ p * survInv M p ((1 + θ) * M.c / p) ∧
        IsFixedPriceOptimal M θ lam p (survInv M p ((1 + θ) * M.c / p)) (thresholdR lam rbar)
          (survInv M p ((1 + θ) * M.c / p)) id ∧
        (∫ ε, (revenue M p (survInv M p ((1 + θ) * M.c / p)) ε -
            thresholdR lam rbar (revenue M p (survInv M p ((1 + θ) * M.c / p)) ε)) ∂M.μ) =
          θ * M.c * survInv M p ((1 + θ) * M.c / p)) ∧
    (θ * M.c < lam * p → lam * (1 + θ) < θ →
      ∃ rbar, 0 ≤ rbar ∧ rbar ≤ p * survInv M p ((1 + θ) * M.c / p) ∧
        IsFixedPriceOptimal M θ lam p (survInv M p ((1 + θ) * M.c / p)) (thresholdR lam rbar)
          (survInv M p ((1 + θ) * M.c / p)) id ∧
        (∫ ε, (revenue M p (survInv M p ((1 + θ) * M.c / p)) ε -
            thresholdR lam rbar (revenue M p (survInv M p ((1 + θ) * M.c / p)) ε)) ∂M.μ) =
          lam * expRevenue M p (survInv M p (θ * M.c / (lam * p))) +
            θ * M.c * (survInv M p ((1 + θ) * M.c / p) - survInv M p (θ * M.c / (lam * p))) ∧
        θ * M.c * survInv M p ((1 + θ) * M.c / p) <
          lam * expRevenue M p (survInv M p (θ * M.c / (lam * p))) +
            θ * M.c * (survInv M p ((1 + θ) * M.c / p) - survInv M p (θ * M.c / (lam * p)))) ∧
    (θ ≤ lam * (1 + θ) → M.c ≤ (1 - lam) * p →
      IsFixedPriceOptimal M θ lam p (survInv M p (M.c / ((1 - lam) * p)))
        (thresholdR lam (p * survInv M p (M.c / ((1 - lam) * p))))
        (survInv M p (M.c / ((1 - lam) * p))) id ∧
      IsFixedPriceOptimal M θ lam p (survInv M p (M.c / ((1 - lam) * p)))
        (fun r => (1 - lam) * r) (survInv M p (M.c / ((1 - lam) * p))) id) ∧
    (¬ ((lam * p ≤ θ * M.c ∧ (1 + θ) * M.c < p) ∨ (θ * M.c < lam * p ∧ lam * (1 + θ) < θ) ∨
        (θ ≤ lam * (1 + θ) ∧ M.c ≤ (1 - lam) * p)) →
      ∃ rbar, 0 ≤ rbar ∧ IsFixedPriceOptimal M θ lam p 0 (thresholdR lam rbar) 0 id) ∧
    (∀ lam₁ lam₂ r₁ r₂ : ℝ, 0 ≤ lam₁ → lam₁ < lam₂ → lam₂ * p ≤ θ * M.c → (1 + θ) * M.c < p →
      r₁ ∈ Set.Icc 0 (p * survInv M p ((1 + θ) * M.c / p)) →
      r₂ ∈ Set.Icc 0 (p * survInv M p ((1 + θ) * M.c / p)) →
      (∫ ε, (revenue M p (survInv M p ((1 + θ) * M.c / p)) ε -
          thresholdR lam₁ r₁ (revenue M p (survInv M p ((1 + θ) * M.c / p)) ε)) ∂M.μ) =
        θ * M.c * survInv M p ((1 + θ) * M.c / p) →
      (∫ ε, (revenue M p (survInv M p ((1 + θ) * M.c / p)) ε -
          thresholdR lam₂ r₂ (revenue M p (survInv M p ((1 + θ) * M.c / p)) ε)) ∂M.μ) =
        θ * M.c * survInv M p ((1 + θ) * M.c / p) →
      r₁ < r₂) ∧
    (∀ lam₁ lam₂ r₁ r₂ : ℝ, θ * M.c < lam₁ * p → lam₁ < lam₂ → lam₂ * (1 + θ) < θ →
      r₁ ∈ Set.Icc 0 (p * survInv M p ((1 + θ) * M.c / p)) →
      r₂ ∈ Set.Icc 0 (p * survInv M p ((1 + θ) * M.c / p)) →
      (∫ ε, (revenue M p (survInv M p ((1 + θ) * M.c / p)) ε -
          thresholdR lam₁ r₁ (revenue M p (survInv M p ((1 + θ) * M.c / p)) ε)) ∂M.μ) =
        lam₁ * expRevenue M p (survInv M p (θ * M.c / (lam₁ * p))) +
          θ * M.c * (survInv M p ((1 + θ) * M.c / p) - survInv M p (θ * M.c / (lam₁ * p))) →
      (∫ ε, (revenue M p (survInv M p ((1 + θ) * M.c / p)) ε -
          thresholdR lam₂ r₂ (revenue M p (survInv M p ((1 + θ) * M.c / p)) ε)) ∂M.μ) =
        lam₂ * expRevenue M p (survInv M p (θ * M.c / (lam₂ * p))) +
          θ * M.c * (survInv M p ((1 + θ) * M.c / p) - survInv M p (θ * M.c / (lam₂ * p))) →
      r₁ < r₂) := by sorry

end RetailTheft
