-- Prove2me | Theorems.Thm_SupplyChainTheory_bullwhip_cov_term_vanishes
-- name    : SupplyChainTheory.bullwhip_cov_term_vanishes
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:02:37.133898+00:00
-- url     : https://prove2.me/theorems/dabd9da2-9712-405b-be1e-80e5987d90f3
-- title:
--   The covariance term (13.12) of $\mathrm{Var}[Q_t]$ vanishes
-- statement:
--   In the variance decomposition (13.11) of the order $Q_t$, the cross term between the demand
--   part $(1 + L/m)D_{t-1} - (L/m)D_{t-m-1}$ and the safety-stock part
--   $\hat\sigma^L_{et} - \hat\sigma^L_{e,t-1}$ is zero: for $m \ge 1$,
--
--   $$ \mathrm{Cov}\Big[\Big(1 + \frac{L}{m}\Big)D_{t-1} - \frac{L}{m}D_{t-m-1},\ \hat\sigma^L_{et} - \hat\sigma^L_{e,t-1}\Big] \;=\; 0. $$
--
--   The book expands the covariance into four terms (Eq. 13.12): two vanish by Lemma 13.1
--   directly, and the other two, $\mathrm{Cov}[D_{t-1}, \hat\sigma^L_{e,t-1}]$ and
--   $\mathrm{Cov}[D_{t-m-1}, \hat\sigma^L_{et}]$, are reduced to instances of Lemma 13.1 through the
--   recursion (13.1) and the independence of the errors from the demands (the second reduction
--   divides by $\rho$; both covariances are in fact zero for every $\rho$ by the same symmetry
--   argument that proves the lemma). Without this step the bound of Theorem 13.2 would carry an
--   uncontrolled cross term.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 545, Sect. 13.2.2, Eq. (13.12) and the derivation ending 'Therefore, we can ignore the Cov[.] term in (13.11)'

import Definitions.Def_SupplyChainTheory_bullwhip

namespace SupplyChainTheory

theorem bullwhip_cov_term_vanishes {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : AR1Demand P) (C : ℝ) (L m : ℕ) (hm : 0 < m)
    (t : ℤ) :
    ProbabilityTheory.covariance
      (fun ω => (1 + (L : ℝ) / m) * X.D (t - 1) ω - ((L : ℝ) / m) * X.D (t - m - 1) ω)
      (fun ω => X.sigmaHat C m t ω - X.sigmaHat C m (t - 1) ω) P = 0 := by sorry

end SupplyChainTheory
