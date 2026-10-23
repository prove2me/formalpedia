-- Prove2me | Theorems.Thm_SLPEPricing_Regret_lemma_3
-- name    : SLPEPricing.Regret.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:33:23.981971+00:00
-- url     : https://prove2.me/theorems/7c8224fb-3c29-402b-ba29-3c8cede2bd1e
-- title:
--   Lemma 3, p. 17 — the two-point finite differences of round i are within ½K₁Δ_i²/12 of d′ at the midpoints
-- statement:
--   Consider round $i\ge1$ of SLPE, with prices $p^L_i<p^M_i<p^H_i$ spaced $\Delta_i$ apart, on a noise realisation $\epsilon$ and pair selector for which Assumption 2 holds in round $i$: the selected periods $a,b,b',c$ lie in the $p^L$-, $p^M$-, $p^M$- and $p^H$-blocks and $\epsilon_a=\epsilon_b$, $\epsilon_{b'}=\epsilon_c$. Write $D_{L^*}(p^L_i),D_{M_1^*}(p^M_i),D_{M_2^*}(p^M_i),D_{H^*}(p^H_i)$ for the demands observed at these periods. Let $d$ be three times continuously differentiable with $|d^{(k)}|\le K_1$ ($k\le3$) on $[-1,2]$, and suppose $[p^L_i,p^H_i]\subseteq[-1,2]$, $\mu>0$, $\rho>0$, $T\ge2$. Then
--   $$\left|\frac{D_{M_1^*}(p^M_i)-D_{L^*}(p^L_i)}{p^M_i-p^L_i}-d'\Big(\frac{p^M_i+p^L_i}2\Big)\right|\le\frac12K_1\frac{\Delta_i^2}{12}\qquad(9)$$
--   and
--   $$\left|\frac{D_{H^*}(p^H_i)-D_{M_2^*}(p^M_i)}{\Delta_i}-d'\Big(\frac{p^M_i+p^H_i}2\Big)\right|\le\frac12K_1\frac{\Delta_i^2}{12}.\qquad(10)$$
--
--   Because each pair carries identical noise, the finite differences are free of stochastic error and approximate the demand gradient to order $\Delta_i^2$; this is the source of SLPE's fast shrinking of the price range.
--
--   **Formalization Note** Rounds are 1-based, periods 0-based. The observations are those the policy records in round $i$ (`roundObs`), $d(\cdot)+\epsilon_t$ at round $i$'s block price. The paper takes $K_1$ on $[0,1]$ and the prices as feasible; since SLPE can charge prices outside $[0,1]$, the bound is taken on $[-1,2]$ and the containment $[p^L_i,p^H_i]\subseteq[-1,2]$ is a hypothesis. The "Furthermore" sentence of the lemma (the pairs satisfy Assumption 2) is the hypothesis on round $i$.
-- source:
--   Perakis & Singhvi, Dynamic Pricing with Unknown Non-Parametric Demand and Limited Price Changes, SSRN 3336949 (PDF of 2020-07-03), p. 17, Lemma 3, Eqs. (9)–(10) (proof App. C, pp. 39–40)

import Mathlib
import Definitions.Def_SLPEPricing_Regret_Model

namespace SLPEPricing.Regret

/-- Lemma 3 (p. 17), for round `i ≥ 1` of SLPE. If the selected periods
`(a, b, b', c) = sel i` satisfy Assumption 2 in round `i` and round `i`'s price range lies in
`[-1, 2]`, where `K₁` bounds `|d^{(k)}|`, `k ≤ 3`, then the two-point finite differences
`(D_{M₁*}(p^M_i) - D_{L*}(p^L_i))/(p^M_i - p^L_i)` and `(D_{H*}(p^H_i) - D_{M₂*}(p^M_i))/Δ_i`
are within `(1/2) K₁ Δ_i²/12` of `d'` at the midpoints. -/
theorem lemma_3 (d : ℝ → ℝ) (K₁ μ ρ : ℝ) (hd : ContDiff ℝ 3 d)
    (hK₁ : ∀ k ≤ 3, ∀ p ∈ Set.Icc (-1 : ℝ) 2, |iteratedDeriv k d p| ≤ K₁)
    (hμ : 0 < μ) (hρ : 0 < ρ)
    (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ) (sel : ℕ → ℕ × ℕ × ℕ × ℕ) (ε : ℕ → ℝ)
    (T : ℕ) (hT : 2 ≤ T) (i : ℕ) (hi : 1 ≤ i)
    (hA2 : Assumption2At μ ρ T sel ε i)
    (hdom : Set.Icc (pL d μ ρ amax sel ε T i) (pH d μ ρ amax sel ε T i) ⊆ Set.Icc (-1) 2) :
    |(roundObs d μ ρ amax sel ε T i (sel i).2.1 - roundObs d μ ρ amax sel ε T i (sel i).1) /
        (pM d μ ρ amax sel ε T i - pL d μ ρ amax sel ε T i) -
        deriv d ((pM d μ ρ amax sel ε T i + pL d μ ρ amax sel ε T i) / 2)| ≤
      1 / 2 * K₁ * (Delta μ i ^ 2 / 12) ∧
    |(roundObs d μ ρ amax sel ε T i (sel i).2.2.2 - roundObs d μ ρ amax sel ε T i (sel i).2.2.1) /
        Delta μ i -
        deriv d ((pM d μ ρ amax sel ε T i + pH d μ ρ amax sel ε T i) / 2)| ≤
      1 / 2 * K₁ * (Delta μ i ^ 2 / 12) := by sorry

end SLPEPricing.Regret
