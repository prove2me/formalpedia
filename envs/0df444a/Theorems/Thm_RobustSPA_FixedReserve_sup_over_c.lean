-- Prove2me | Theorems.Thm_RobustSPA_FixedReserve_sup_over_c
-- name    : RobustSPA.FixedReserve.sup_over_c
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:13:56.877913+00:00
-- url     : https://prove2.me/theorems/a3f25651-e430-4926-98ed-3ab514c346b1
-- title:
--   Proof of Proposition 5, p. App-10 — for n ≥ 2, max over c ∈ [(n−1)/n, 1] of rcⁿ + (1−r)(ncⁿ⁻¹ − ncⁿ): value at c* for r ≤ ½, r for r ≥ ½
-- statement:
--   Let $n\ge 2$, $r\in[0,1]$, and
--   $$g(c)=r\,c^n+(1-r)\big(n c^{n-1}-n c^n\big),\qquad c\in\Big[\tfrac{n-1}{n},\,1\Big].$$
--
--   1. If $r\le\frac12$, the point $c^*=\dfrac{(1-r)(n-1)}{(1-r)n-r}$ lies in $\big[\frac{n-1}{n},1\big]$, and $g(c^*)$ is the maximum of $g$ on this interval:
--   $$\max_{c\in[\frac{n-1}{n},1]} g(c)=g(c^*)=\frac{(1-r)^n(n-1)^{n-1}}{((1-r)n-r)^{n-1}}.$$
--   2. If $r\ge\frac12$, the maximum is attained at $c=1$ and equals $g(1)=r$.
--
--   In the proof of Proposition 5 this one-variable maximization yields the worst-case regret of $\mathrm{SPA}(r)$ over i.i.d. laws: $c$ is the probability mass Nature places just below the reserve.
-- source:
--   Anunrojwong, Balseiro & Besbes, On the Robustness of Second-Price Auctions in Prior-Independent Mechanism Design, arXiv:2204.10478v5, p. App-10, Proof of Proposition 5 (optimization over c)

import Mathlib
import Definitions.Def_RobustSPA_FixedReserve_Setting

open MeasureTheory

namespace RobustSPA.FixedReserve

/-- Proof of Proposition 5, p. App-10: for `n ≥ 2` and `r ∈ [0,1]`, the maximum of
`g(c) = r cⁿ + (1 − r)(n c^{n−1} − n cⁿ)` over `c ∈ [(n−1)/n, 1]` is attained at
`c* = (1−r)(n−1)/((1−r)n−r) ∈ [(n−1)/n, 1]` with value `(1−r)ⁿ(n−1)^{n−1}/((1−r)n−r)^{n−1}`
when `r ≤ 1/2`, and at `c = 1` with value `r` when `r ≥ 1/2`. -/
theorem sup_over_c (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    let g : ℝ → ℝ := fun c => r * c ^ n + (1 - r) * ((n : ℝ) * c ^ (n - 1) - (n : ℝ) * c ^ n)
    let cstar : ℝ := (1 - r) * ((n : ℝ) - 1) / ((1 - r) * n - r)
    (r ≤ 1 / 2 →
      cstar ∈ Set.Icc (((n : ℝ) - 1) / n) 1 ∧
      g cstar = (1 - r) ^ n * ((n : ℝ) - 1) ^ (n - 1) / ((1 - r) * n - r) ^ (n - 1) ∧
      IsGreatest (g '' Set.Icc (((n : ℝ) - 1) / n) 1)
        ((1 - r) ^ n * ((n : ℝ) - 1) ^ (n - 1) / ((1 - r) * n - r) ^ (n - 1))) ∧
    (1 / 2 ≤ r → g 1 = r ∧ IsGreatest (g '' Set.Icc (((n : ℝ) - 1) / n) 1) r) := by sorry

end RobustSPA.FixedReserve
