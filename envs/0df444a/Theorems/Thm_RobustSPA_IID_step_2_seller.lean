-- Prove2me | Theorems.Thm_RobustSPA_IID_step_2_seller
-- name    : RobustSPA.IID.step_2_seller
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:08.70031+00:00
-- url     : https://prove2.me/theorems/1bf50f10-f204-4f01-9bab-575937463da2
-- title:
--   Proof of Theorem 1, Step 2, p. 17 — Seller's optimality: R_n(m*_n, F*_n) ≤ R_n(m, F*_n) for every DSIC m
-- statement:
--   Let $n \ge 1$, let $r^*_n \in (0, 1/n)$ solve $(1-r)^{n-1} + \log r + \sum_{k=1}^{n-1} (1-r)^k/k = 0$, let $m^*_n = \mathrm{SPA}(\Phi^*_n)$ be the second-price auction whose random reserve has CDF $\Phi^*_n$, and let $\boldsymbol F^*_n = (F^*_n)^{\otimes n}$ be the i.i.d. isorevenue law with marginal CDF $F^*_n(v) = 1 - r^*_n/v$ on $[r^*_n, 1)$, $F^*_n(1) = 1$. Then for every DSIC mechanism $m \in \mathcal M$,
--   $$R_n(m^*_n, \boldsymbol F^*_n) \le R_n(m, \boldsymbol F^*_n).$$
--
--   This is the second saddle-point inequality: against the isorevenue law, $m^*_n$ maximizes expected revenue among all DSIC mechanisms (not only second-price auctions). Since $\boldsymbol F^*_n$ has an atom at $1$, standard Bayesian optimal-auction results do not apply directly.
--
--   **Formalization Note.** DSIC mechanisms are those of the setting file: (IR), (IC), (AC) on $[0,1]^n$, measurable rules and bounded payments.
-- source:
--   Anunrojwong, Balseiro & Besbes, On the Robustness of Second-Price Auctions in Prior-Independent Mechanism Design, arXiv:2204.10478v5, p. 17, Proof of Theorem 1, Step 2 (Seller's optimality); details pp. App-3–App-4 (PDF pp. 33–34)

import Mathlib
import Definitions.Def_RobustSPA_IID_Setting

namespace RobustSPA.IID

open MeasureTheory

/-- Proof of Theorem 1, Step 2 (Seller's optimality, p. 17). With `r*_n ∈ (0, 1/n)` the root of
the `r*`-equation, `ρ` the reserve law with CDF `Φ*_n` and `G` the isorevenue marginal with CDF
`F*_n`, every DSIC mechanism `m` has `Rₙ(m*_n, F*_n) ≤ Rₙ(m, F*_n)` where `m*_n = SPA(Φ*_n)`. -/
theorem step_2_seller (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) (1 / n))
    (hroot : rEq n r = 0) (ρ G : ProbabilityMeasure ℝ)
    (hρ : ∀ t, cdfOf ρ t = PhiStar n r t) (hG : ∀ t, cdfOf G t = isoCDF r t) :
    ∀ m : Mechanism n, m.IsDSIC →
      regret (SPA (ρ : Measure ℝ)) (Measure.pi fun _ : Fin n => (G : Measure ℝ)) ≤
        regret m (Measure.pi fun _ : Fin n => (G : Measure ℝ)) := by sorry

end RobustSPA.IID
