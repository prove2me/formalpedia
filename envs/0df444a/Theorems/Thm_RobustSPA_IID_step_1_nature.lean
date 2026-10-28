-- Prove2me | Theorems.Thm_RobustSPA_IID_step_1_nature
-- name    : RobustSPA.IID.step_1_nature
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:13:59.374022+00:00
-- url     : https://prove2.me/theorems/f18e5bda-9239-47f7-bcb2-8fc089458126
-- title:
--   Proof of Theorem 1, Step 1, p. 17 — Nature's optimality: R_n(Φ*_n, F) ≤ R_n(Φ*_n, F*_n) for every i.i.d. F
-- statement:
--   Let $n \ge 1$, let $r^*_n \in (0, 1/n)$ solve $(1-r)^{n-1} + \log r + \sum_{k=1}^{n-1} (1-r)^k/k = 0$, let $\Phi^*_n$ be the reserve law of Theorem 1 (CDF $\Phi^*_n$) and let $\boldsymbol F^*_n = (F^*_n)^{\otimes n}$ be the i.i.d. isorevenue law with marginal CDF $F^*_n(v) = 1 - r^*_n/v$ on $[r^*_n, 1)$, $F^*_n(1) = 1$. Then for every i.i.d. law $\boldsymbol F \in \mathcal F_{\mathrm{iid}}$ on $[0,1]^n$,
--   $$R_n(\Phi^*_n, \boldsymbol F) \le R_n(\Phi^*_n, \boldsymbol F^*_n),$$
--   where $R_n(\Phi, \boldsymbol F)$ is the regret of the second-price auction with random reserve $\Phi$.
--
--   This is the first saddle-point inequality: against the mechanism $m^*_n = \mathrm{SPA}(\Phi^*_n)$, the isorevenue law is a worst case among i.i.d. laws.
-- source:
--   Anunrojwong, Balseiro & Besbes, On the Robustness of Second-Price Auctions in Prior-Independent Mechanism Design, arXiv:2204.10478v5, p. 17, Proof of Theorem 1, Step 1 (Nature's optimality)

import Mathlib
import Definitions.Def_RobustSPA_IID_Setting

namespace RobustSPA.IID

open MeasureTheory

/-- Proof of Theorem 1, Step 1 (Nature's optimality, p. 17). With `r*_n ∈ (0, 1/n)` the root of
the `r*`-equation, `ρ` the reserve law with CDF `Φ*_n` and `G` the isorevenue marginal with CDF
`F*_n`, every i.i.d. law `F` on `[0,1]ⁿ` gives `Rₙ(Φ*_n, F) ≤ Rₙ(Φ*_n, F*_n)`. -/
theorem step_1_nature (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) (1 / n))
    (hroot : rEq n r = 0) (ρ G : ProbabilityMeasure ℝ)
    (hρ : ∀ t, cdfOf ρ t = PhiStar n r t) (hG : ∀ t, cdfOf G t = isoCDF r t) :
    ∀ μ ∈ Fiid n, regret (SPA (ρ : Measure ℝ)) μ ≤
      regret (SPA (ρ : Measure ℝ)) (Measure.pi fun _ : Fin n => (G : Measure ℝ)) := by sorry

end RobustSPA.IID
