-- Prove2me | Theorems.Thm_RobustSPA_FixedReserve_regret_spa_fixed_iid
-- name    : RobustSPA.FixedReserve.regret_spa_fixed_iid
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:09.505218+00:00
-- url     : https://prove2.me/theorems/989e8591-a220-4e76-a76b-2d648054fdd0
-- title:
--   Proof of Proposition 5, p. App-10 — regret of SPA(r) under i.i.d. F: rF₋(r)ⁿ − ∫₀ʳ F(v)ⁿdv + ∫ᵣ¹ (nF(v)ⁿ⁻¹ − nF(v)ⁿ)dv
-- statement:
--   Let $n\ge 1$ buyers have i.i.d. valuations drawn from a probability law $G$ on $[0,1]$, with CDF $F(v)=\Pr(v_i\le v)$ and left limit $F_-(r)=\Pr(v_i<r)$. Let $r\in[0,1]$ and let $\mathrm{SPA}(r)$ be the second-price auction with fixed reserve $r$ (the highest bidder buys if her bid is at least $r$, at price $\max(v^{(2)},r)$). Then the regret of $\mathrm{SPA}(r)$ under $F^{\otimes n}$ is
--
--   $$R_n(\mathrm{SPA}(r),F)=r\,F_-(r)^n-\int_0^r F(v)^n\,dv+\int_r^1\big(nF(v)^{n-1}-nF(v)^n\big)\,dv.$$
--
--   This expresses the regret through the marginal CDF alone; the worst case over $\mathcal F_{\mathrm{iid}}$ is then a one-dimensional optimization over the value of $F$ around the reserve.
--
--   **Formalization Note** The paper prints this display with a supremum over $F\in\mathcal F_{\mathrm{iid}}([0,1])$ on the left; the right side depends on $F$, and what the computation shows is the regret of the given $F$, which is what is stated here. The integrals over $[0,r]$ and $(r,1]$ are interval integrals (endpoints are Lebesgue-null).
-- source:
--   Anunrojwong, Balseiro & Besbes, On the Robustness of Second-Price Auctions in Prior-Independent Mechanism Design, arXiv:2204.10478v5, p. App-10, Proof of Proposition 5 (display 'Together, we have')

import Mathlib
import Definitions.Def_RobustSPA_FixedReserve_Setting

open MeasureTheory

namespace RobustSPA.FixedReserve

/-- Proof of Proposition 5, p. App-10: the regret of `SPA(r)` under `n` i.i.d. valuations with
law `G` on `[0,1]`, writing `F(v) = G((-∞, v])` and `F₋(r) = G((-∞, r))`, is
`r F₋(r)ⁿ − ∫_{[0,r]} F(v)ⁿ dv + ∫_{(r,1]} (n F(v)^{n−1} − n F(v)ⁿ) dv`. -/
theorem regret_spa_fixed_iid (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (G : ProbabilityMeasure ℝ) (hG : (G : Measure ℝ) (Set.Icc 0 1)ᶜ = 0) :
    regret (SPA (Measure.dirac r)) (Measure.pi fun _ : Fin n => (G : Measure ℝ)) =
      r * ((G : Measure ℝ) (Set.Iio r)).toReal ^ n
        - ∫ v in (0)..r, cdfOf (G : Measure ℝ) v ^ n
        + ∫ v in r..1, ((n : ℝ) * cdfOf (G : Measure ℝ) v ^ (n - 1)
            - (n : ℝ) * cdfOf (G : Measure ℝ) v ^ n) := by sorry

end RobustSPA.FixedReserve
