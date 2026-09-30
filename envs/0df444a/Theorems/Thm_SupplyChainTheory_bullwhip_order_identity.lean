-- Prove2me | Theorems.Thm_SupplyChainTheory_bullwhip_order_identity
-- name    : SupplyChainTheory.bullwhip_order_identity
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:01:34.794575+00:00
-- url     : https://prove2.me/theorems/08c68670-9e73-4d3c-84f6-45adf97224e9
-- title:
--   $Q_t = (1 + L/m)\,D_{t-1} - (L/m)\,D_{t-m-1} + z_\alpha(\hat\sigma^L_{et} - \hat\sigma^L_{e,t-1})$
-- statement:
--   Under the moving-average base-stock policy of Sect. 13.2.2 with $m \ge 1$, the order placed in
--   period $t$, $Q_t = S_t - S_{t-1} + D_{t-1}$, equals
--
--   $$ Q_t \;=\; \Big(1 + \frac{L}{m}\Big) D_{t-1} - \frac{L}{m}\, D_{t-m-1}
--      + z_\alpha\big(\hat\sigma^L_{et} - \hat\sigma^L_{e,t-1}\big), $$
--
--   for every outcome: the two moving averages differ only in their first and last terms, so
--   $\hat\mu^L_t - \hat\mu^L_{t-1} = L(D_{t-1} - D_{t-m-1})/m$. This is the algebra that turns the
--   ordering rule into a statement about two demands $m$ periods apart, and it is why the lead time
--   magnifies the variability: the coefficient of $D_{t-1}$ grows with $L/m$.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 544, Sect. 13.2.2, the display rewriting Qt = St - St-1 + Dt-1

import Definitions.Def_SupplyChainTheory_bullwhip

namespace SupplyChainTheory

theorem bullwhip_order_identity {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (X : AR1Demand P) (C z : ℝ) (L m : ℕ) (hm : 0 < m) (t : ℤ) (ω : Ω) :
    X.order C z L m t ω
      = (1 + (L : ℝ) / m) * X.D (t - 1) ω - ((L : ℝ) / m) * X.D (t - m - 1) ω
        + z * (X.sigmaHat C m t ω - X.sigmaHat C m (t - 1) ω) := by sorry

end SupplyChainTheory
