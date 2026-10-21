-- Prove2me | Theorems.Thm_RetailerMarketplace_Entry_dPi_formula
-- name    : RetailerMarketplace.Entry.dPi_formula
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:31.406598+00:00
-- url     : https://prove2.me/theorems/0f6b828a-d88b-43f6-9299-08f3d9953091
-- title:
--   Proof of Proposition 2, p. 14 — Δπ = (v − v_T)(1 − f)(λ − f(1 − λ))/(1 − f(1 − λ)), positive for v > v_T, increasing in v, decreasing in f
-- statement:
--   Let $c>0$, $f\in[0,1)$ and $\lambda\in[\tfrac12,1]$ (Assumption 1). $M$'s marginal profitability of entering a marketplace product is $\Delta\pi_M^{SBMT-SBT}(v)=\pi_M^{SBMT}(v)-\pi_M^{SBT}(v)$. Then
--   1. for every $v$,
--   $$\Delta\pi_M^{SBMT-SBT}(v)=(v-v_T)\,\frac{(1-f)(\lambda-f(1-\lambda))}{1-f(1-\lambda)};$$
--   2. $\Delta\pi_M^{SBMT-SBT}(v)>0$ for every $v>v_T$;
--   3. $v\mapsto\Delta\pi_M^{SBMT-SBT}(v)$ is strictly increasing;
--   4. it is strictly decreasing in the fee: if $0\le f_1<f_2<1$ and $v(1-f_2)\ge c$ (a marketplace product at the larger fee), then $\Delta\pi_M^{SBMT-SBT}(v)$ at fee $f_2$ is smaller than at fee $f_1$.
--
--   These are the properties of $\Delta\pi$ the proof of Proposition 2 uses to rank products for entry.
--
--   **Formalization Note** The page says $\Delta\pi$ "is positive if $\lambda>f/(1+f)$"; because of the factor $v-v_T$ it vanishes at $v=v_T$, so positivity is stated for $v>v_T$. "Decreases in $f$" is stated on the products that are marketplace products at the larger fee, where it holds strictly; outside that region the two factors can change sign.
-- source:
--   Hervas-Drane & Shelegia, Retailer-Led Marketplaces, Management Science (2025), Articles in Advance, doi:10.1287/mnsc.2023.00315, p. 14 (PDF p. 16), proof of Proposition 2, display defining Δπ

import Mathlib
import Definitions.Def_RetailerMarketplace_Entry_Model

namespace RetailerMarketplace.Entry

/-- Proof of Proposition 2, p. 14: M's marginal profitability of entering a marketplace product is
`Δπ_M^{SBMT-SBT}(v) = (v - v_T)(1 - f)(λ - f(1 - λ))/(1 - f(1 - λ))`; it is positive for `v > v_T`,
strictly increasing in `v`, and strictly decreasing in the fee `f` on the products that are
marketplace products at the larger fee. -/
theorem dPi_formula (c f lam : ℝ) (hc : 0 < c) (hf : f ∈ Set.Ico (0 : ℝ) 1)
    (hlam : lam ∈ Set.Icc (1 / 2 : ℝ) 1) :
    (∀ v : ℝ, dPi c f lam v = (v - vT c f) * ((1 - f) * (lam - f * (1 - lam))) / (1 - f * (1 - lam))) ∧
      (∀ v : ℝ, vT c f < v → 0 < dPi c f lam v) ∧
      StrictMono (dPi c f lam) ∧
      (∀ f₁ f₂ v : ℝ, 0 ≤ f₁ → f₁ < f₂ → f₂ < 1 → v ∈ mp c f₂ →
        dPi c f₂ lam v < dPi c f₁ lam v) := by sorry

end RetailerMarketplace.Entry
