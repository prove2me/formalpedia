-- Prove2me | Theorems.Thm_SupplyChainTheory_bullwhip_demand_part_variance
-- name    : SupplyChainTheory.bullwhip_demand_part_variance
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:03:09.932495+00:00
-- url     : https://prove2.me/theorems/93d7b541-0669-45ac-b013-8c187cdbc3de
-- title:
--   $\mathrm{Var}\big[(1 + L/m)D_{t-1} - (L/m)D_{t-m-1}\big] = \big(1 + (2L/m + 2L^2/m^2)(1 - \rho^m)\big)\mathrm{Var}[D]$
-- statement:
--   For the stationary AR(1) demand and $m \ge 1$, the variance of the demand part of the order is
--
--   $$ \mathrm{Var}\Big[\Big(1 + \frac{L}{m}\Big)D_{t-1} - \frac{L}{m}D_{t-m-1}\Big]
--      \;=\; \Big(1 + \Big(\frac{2L}{m} + \frac{2L^2}{m^2}\Big)(1 - \rho^m)\Big)\mathrm{Var}[D_t]. $$
--
--   It follows from $\mathrm{Var}[aX + bY] = a^2\mathrm{Var}[X] + b^2\mathrm{Var}[Y] + 2ab\,\mathrm{Cov}[X, Y]$
--   (Eq. 13.10) with $\mathrm{Cov}[D_{t-1}, D_{t-m-1}] = \rho^m\mathrm{Var}[D]$ (Eq. 13.4), since
--   $(1 + L/m)^2 + (L/m)^2 = 1 + 2L/m + 2L^2/m^2$. Together with the vanishing of the cross term it
--   gives $\mathrm{Var}[Q_t] = (\cdots)\mathrm{Var}[D] + z_\alpha^2\mathrm{Var}[\hat\sigma^L_{et} - \hat\sigma^L_{e,t-1}]$,
--   from which Theorem 13.2 is read off.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 545, Sect. 13.2.2, the display computing Var[Qt] from (13.10) and (13.4)

import Definitions.Def_SupplyChainTheory_bullwhip

namespace SupplyChainTheory

theorem bullwhip_demand_part_variance {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (X : AR1Demand P)
    (L m : ℕ) (hm : 0 < m) (t : ℤ) :
    ProbabilityTheory.variance
        (fun ω => (1 + (L : ℝ) / m) * X.D (t - 1) ω - ((L : ℝ) / m) * X.D (t - m - 1) ω) P
      = (1 + (2 * (L : ℝ) / m + 2 * (L : ℝ) ^ 2 / (m : ℝ) ^ 2) * (1 - X.rho ^ m))
          * ProbabilityTheory.variance (X.D t) P := by sorry

end SupplyChainTheory
