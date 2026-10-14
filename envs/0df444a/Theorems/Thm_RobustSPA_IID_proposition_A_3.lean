-- Prove2me | Theorems.Thm_RobustSPA_IID_proposition_A_3
-- name    : RobustSPA.IID.proposition_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:13:57.235353+00:00
-- url     : https://prove2.me/theorems/0f9049a7-1d0c-4837-b662-9a82b5306669
-- title:
--   Proposition A-3, p. App-2 — r*_n ∈ (0, 1/n) unique; Φ*_n solves (ODE-Φ), Φ*_n(r*_n) = 0, Φ*_n(1) = 1, and R_n(Φ*_n, F*_n) equals the value
-- statement:
--   Let $n \ge 1$.
--
--   1. The equation $(1-r)^{n-1} + \log r + \sum_{k=1}^{n-1} (1-r)^k/k = 0$ has a solution $r^*_n \in (0, 1/n)$, and it is the only solution in $(0,1)$.
--   2. For this $r^*_n$, the function
--   $$\Phi^*_n(v) = \Big(\frac{v}{v-r^*_n}\Big)^{n-1}\log\Big(\frac{v}{r^*_n}\Big) - \sum_{k=1}^{n-1}\frac1k\Big(\frac{v}{v-r^*_n}\Big)^{n-1-k}$$
--   equals the series $\sum_{k=n}^{\infty} \frac1k\big(\frac{v-r^*_n}{v}\big)^{k-(n-1)}$ for $v \in (r^*_n, 1]$ and satisfies the ODE (ODE-$\Phi$) on $(r^*_n, 1)$:
--   $$(\Phi^*_n)'(v) + \frac{(n-1)r^*_n}{v(v-r^*_n)}\Phi^*_n(v) = \frac1v,$$
--   together with $\Phi^*_n(r^*_n) = 0$ (as the limit $v \downarrow r^*_n$) and $\Phi^*_n(1) = 1$.
--   3. Let $F^*_n$ be the isorevenue marginal, $F^*_n(v) = 1 - r^*_n/v$ for $v \in [r^*_n, 1)$ and $F^*_n(1) = 1$, and $\boldsymbol F^*_n = (F^*_n)^{\otimes n}$. For any reserve law with CDF $\Phi^*_n$,
--   $$R_n(\Phi^*_n, \boldsymbol F^*_n) = (1-r^*_n)^{n-1} - \int_{r^*_n}^1 \Big(1 - \frac{r^*_n}{v}\Big)^{n-1} dv.$$
--
--   The proposition produces the candidate saddle point $(\mathrm{SPA}(\Phi^*_n), \boldsymbol F^*_n)$ and its value; Steps 1 and 2 of the proof of Theorem 1 verify the saddle inequalities.
--
--   **Formalization Note.** The page states uniqueness in $(0, 1/n)$; the proof (p. App-7) shows the left side increases on $(0,1/n)$ and decreases on $(1/n, 1)$ towards $0$, so the root is unique in $(0,1)$, which is what is stated. The closed form of $\Phi^*_n$ is a $0/0$ expression at $v = r^*_n$; $\Phi^*_n$ is defined as $0$ for $v \le r^*_n$ and $1$ for $v > 1$, and $\Phi^*_n(r^*_n) = 0$ is stated as the right limit. Laws are given by their CDFs. Laws given by a CDF hypothesis exist (Theorem 1 asserts the existence of the reserve law; the isorevenue law is a Stieltjes measure).
-- source:
--   Anunrojwong, Balseiro & Besbes, On the Robustness of Second-Price Auctions in Prior-Independent Mechanism Design, arXiv:2204.10478v5, p. App-2 (PDF p. 32), Proposition A-3 and (ODE-Φ); uniqueness proof p. App-7 (PDF p. 37)

import Mathlib
import Definitions.Def_RobustSPA_IID_Setting

namespace RobustSPA.IID

open MeasureTheory

/-- Proposition A-3 (p. App-2). The `r*`-equation has a root `r*_n ∈ (0, 1/n)`, the only root in
`(0, 1)`. For that root, `Φ*_n(v) = Σ_{k=n}^∞ (1/k) ((v − r*_n)/v)^{k−(n−1)}` on `(r*_n, 1]`,
`Φ*_n` satisfies (ODE-Φ)
`(Φ*)'(v) + (n − 1) r*_n / (v (v − r*_n)) Φ*(v) = 1/v` on `(r*_n, 1)`, tends to `0` as
`v ↓ r*_n`, equals `1` at `v = 1`, and under the i.i.d. isorevenue law `F*_n` (marginal CDF
`1 − r*_n/v` on `[r*_n, 1)`, `1` at `1`) the regret of `SPA(Φ*_n)` is
`(1 − r*_n)^{n−1} − ∫_{r*_n}^1 (1 − r*_n/v)^{n−1} dv`. -/
theorem proposition_A_3 (n : ℕ) (hn : 0 < n) :
    (∃ r ∈ Set.Ioo (0 : ℝ) (1 / n), rEq n r = 0 ∧
      ∀ r' ∈ Set.Ioo (0 : ℝ) 1, rEq n r' = 0 → r' = r) ∧
    ∀ r ∈ Set.Ioo (0 : ℝ) (1 / n), rEq n r = 0 →
      (∀ v ∈ Set.Ioc r 1, HasSum
        (fun j : ℕ => 1 / ((j + n : ℕ) : ℝ) * ((v - r) / v) ^ (j + 1)) (PhiStar n r v)) ∧
      (∀ v ∈ Set.Ioo r 1, HasDerivAt (PhiStar n r)
        (1 / v - ((n : ℝ) - 1) * r / (v * (v - r)) * PhiStar n r v) v) ∧
      Filter.Tendsto (PhiStar n r) (nhdsWithin r (Set.Ioi r)) (nhds 0) ∧
      PhiStar n r 1 = 1 ∧
      ∀ ρ G : ProbabilityMeasure ℝ, (∀ t, cdfOf ρ t = PhiStar n r t) →
        (∀ t, cdfOf G t = isoCDF r t) →
        regret (SPA (ρ : Measure ℝ)) (Measure.pi fun _ : Fin n => (G : Measure ℝ)) =
          value n r := by sorry

end RobustSPA.IID
