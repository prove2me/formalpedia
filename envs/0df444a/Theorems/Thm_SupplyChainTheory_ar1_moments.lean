-- Prove2me | Theorems.Thm_SupplyChainTheory_ar1_moments
-- name    : SupplyChainTheory.ar1_moments
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:00:33.953343+00:00
-- url     : https://prove2.me/theorems/0875cdab-bc74-46cf-8ceb-c98914918172
-- title:
--   Eq. (13.2)-(13.4): mean, variance and autocovariance of the stationary AR(1) demand
-- statement:
--   For the stationary AR(1) demand process $D_t = d + \rho D_{t-1} + \epsilon_t$ with
--   $\epsilon_t \sim N(0, \sigma^2)$ and $-1 < \rho < 1$, for every period $t$ and every lag
--   $k \ge 0$,
--
--   $$ \mathbb{E}[D_t] = \frac{d}{1-\rho}, \qquad \mathrm{Var}[D_t] = \frac{\sigma^2}{1-\rho^2},
--      \qquad \mathrm{Cov}[D_t, D_{t-k}] = \rho^k\,\mathrm{Var}[D_t]. $$
--
--   The book remarks that $d$ is not the mean unless $\rho = 0$, and that these are the
--   steady-state values, the same in every period. The autocovariance is what produces the factor
--   $(1 - \rho^m)$ in Theorem 13.2: the two demands entering the order, $D_{t-1}$ and $D_{t-m-1}$,
--   are $m$ periods apart.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 543, Sect. 13.2.2, Eq. (13.2), (13.3), (13.4)

import Definitions.Def_SupplyChainTheory_bullwhip

namespace SupplyChainTheory

theorem ar1_moments {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : AR1Demand P) (t : ℤ) (k : ℕ) :
    (∫ ω, X.D t ω ∂P) = X.d / (1 - X.rho)
      ∧ ProbabilityTheory.variance (X.D t) P = X.sigma ^ 2 / (1 - X.rho ^ 2)
      ∧ ProbabilityTheory.covariance (X.D t) (X.D (t - k)) P
          = X.rho ^ k * ProbabilityTheory.variance (X.D t) P := by sorry

end SupplyChainTheory
