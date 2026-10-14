-- Prove2me | Theorems.Thm_RobustSPA_FixedReserve_regret_spa_fixed_aff_le
-- name    : RobustSPA.FixedReserve.regret_spa_fixed_aff_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:05.075862+00:00
-- url     : https://prove2.me/theorems/e65f4a13-863b-4afc-b537-9965e2572180
-- title:
--   Proof of Proposition 5, p. App-11 — for n ≥ 2 and exchangeable affiliated F, the regret of SPA(r) is at most the 𝓕_iid worst-case value
-- statement:
--   Let $n\ge 2$, $r\in[0,1]$, and let $\mathbf F$ be an exchangeable and affiliated distribution of the valuations on $[0,1]^n$, i.e. $\mathbf F\in\mathcal F_{\mathrm{aff}}$. Then the regret of the second-price auction with fixed reserve $r$ satisfies
--
--   $$R_n(\mathrm{SPA}(r),\mathbf F)\le \frac{(1-r)^n(n-1)^{n-1}}{((1-r)n-r)^{n-1}}\ \text{ if } r\le\tfrac12,\qquad R_n(\mathrm{SPA}(r),\mathbf F)\le r\ \text{ if } r>\tfrac12,$$
--
--   the worst-case value over i.i.d. laws.
--
--   This is the step that extends Proposition 5 from $\mathcal F_{\mathrm{iid}}$ to $\mathcal F_{\mathrm{aff}}$: affiliation cannot make a fixed-reserve second-price auction worse than the i.i.d. worst case.
-- source:
--   Anunrojwong, Balseiro & Besbes, On the Robustness of Second-Price Auctions in Prior-Independent Mechanism Design, arXiv:2204.10478v5, p. App-11, Proof of Proposition 5 (the class 𝓕_aff)

import Mathlib
import Definitions.Def_RobustSPA_FixedReserve_Setting

open MeasureTheory

namespace RobustSPA.FixedReserve

/-- Proof of Proposition 5, p. App-11 (the class `𝓕_aff`): for `n ≥ 2`, `r ∈ [0,1]` and every
exchangeable affiliated law on `[0,1]ⁿ`, the regret of `SPA(r)` is at most the `𝓕_iid`
worst-case value `wcFixed n r`. -/
theorem regret_spa_fixed_aff_le (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (μ : Measure (Fin n → ℝ)) (hμ : μ ∈ Faff n) :
    regret (SPA (Measure.dirac r)) μ ≤ wcFixed n r := by sorry

end RobustSPA.FixedReserve
