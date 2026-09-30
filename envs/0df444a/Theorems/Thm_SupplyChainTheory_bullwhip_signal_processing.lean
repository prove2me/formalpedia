-- Prove2me | Theorems.Thm_SupplyChainTheory_bullwhip_signal_processing
-- name    : SupplyChainTheory.bullwhip_signal_processing
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:06:27.402579+00:00
-- url     : https://prove2.me/theorems/14a0f232-b4f0-4fe3-921d-be05f8b223bd
-- title:
--   Theorem 13.2: $\mathrm{Var}[Q]/\mathrm{Var}[D] \ge 1 + (2L/m + 2L^2/m^2)(1 - \rho^m)$, with equality when $z_\alpha = 0$
-- statement:
--   **Theorem 13.2.** Demand signal processing creates the bullwhip effect at a single stage.
--
--   A retailer faces the stationary AR(1) demand $D_t = d + \rho D_{t-1} + \epsilon_t$ of
--   Sect. 13.2.2 ($d \ge 0$, $-1 < \rho < 1$, $\epsilon_t$ i.i.d. $N(0,\sigma^2)$), replenishes with
--   lead time $L$, and, not knowing the demand parameters, sets its base-stock level from a moving
--   average of the previous $m \ge 1$ demands: $S_t = \hat\mu^L_t + z_\alpha\hat\sigma^L_{et}$ with
--   $\hat\mu^L_t = L\sum_{i=1}^m D_{t-i}/m$ and $\hat\sigma^L_{et} = C\sqrt{\sum_{i=1}^m e_{t-i}^2/m}$,
--   ordering $Q_t = S_t - S_{t-1} + D_{t-1}$ each period. Then
--
--   $$ \frac{\mathrm{Var}[Q_t]}{\mathrm{Var}[D_t]} \;\ge\; 1 + \Big(\frac{2L}{m} + \frac{2L^2}{m^2}\Big)\big(1 - \rho^m\big), $$
--
--   and the bound is tight when $z_\alpha = 0$: with no safety stock the ratio equals the
--   right-hand side.
--
--   The bound exceeds $1$ whenever $L > 0$, so a positive lead time together with forecasting is
--   enough to make the orders more variable than the demands, even when $\rho = 0$ and the
--   demands are independent. The book draws out the comparative statics: the bound decreases in
--   $m$ (smoother forecasts), increases in $L$, decreases in $\rho$ for $\rho \ge 0$, and for
--   $\rho < 0$ behaves differently for odd and even $m$. Theorems 13.6 and 13.7 apply the same
--   bound stage by stage to a serial supply chain.
--
--   **Formalization Note** The proof runs through the order identity, the autocovariance (13.4),
--   the vanishing of the cross term (Lemma 13.1) and the variance of the demand part, all
--   separate items; the ratio is stated with $\mathrm{Var}[D_t] = \sigma^2/(1-\rho^2) > 0$. The
--   book's constant $C_{L\rho}$ in the estimate of $\hat\sigma$ is a free parameter, which the bound
--   does not involve.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 545, Sect. 13.2.2, Theorem 13.2, Eq. (13.13): 'The bound is tight when z_alpha = 0'; the model is pp. 542-544, Eq. (13.1)-(13.9); after Chen et al. (2000)

import Definitions.Def_SupplyChainTheory_bullwhip

namespace SupplyChainTheory

theorem bullwhip_signal_processing {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : AR1Demand P) (C z : ℝ)
    (L m : ℕ) (hm : 0 < m) (t : ℤ) :
    ProbabilityTheory.variance (X.order C z L m t) P / ProbabilityTheory.variance (X.D t) P
        ≥ 1 + (2 * (L : ℝ) / m + 2 * (L : ℝ) ^ 2 / (m : ℝ) ^ 2) * (1 - X.rho ^ m)
      ∧ (z = 0 →
          ProbabilityTheory.variance (X.order C z L m t) P / ProbabilityTheory.variance (X.D t) P
            = 1 + (2 * (L : ℝ) / m + 2 * (L : ℝ) ^ 2 / (m : ℝ) ^ 2) * (1 - X.rho ^ m)) := by sorry

end SupplyChainTheory
