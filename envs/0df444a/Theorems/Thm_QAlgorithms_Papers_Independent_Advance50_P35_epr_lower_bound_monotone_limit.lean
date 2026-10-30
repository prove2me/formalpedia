-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P35_epr_lower_bound_monotone_limit
-- name    : QAlgorithms.Papers.Independent.Advance50.P35.epr_lower_bound_monotone_limit
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T13:49:21.241994+00:00
-- url     : https://prove2.me/theorems/8ca91f50-7143-4501-bd17-5355db16eeb5
-- title:
--   EPR lower-bound monotonicity and the many-pair limit
-- statement:
--   Fix $0\leq\kappa_0<1$ and a finite signal energy $n\geq0$, for the equal-prior ideal cell $\{\kappa_0,1\}$. For each integer $s\geq1$ define
--
--   $$\Theta_s=\frac{1}{2[1+(n/s)(1-\sqrt{\kappa_0})]^{2s}},\quad Q_s=1-h_2(\Theta_s),\quad\theta=\frac{e^{-2n(1-\sqrt{\kappa_0})}}2,\quad Q_\infty=1-h_2(\theta).$$
--
--   The sequence $Q_s$ is nondecreasing, and
--
--   $$\Theta_s\longrightarrow\theta,\qquad Q_s\longrightarrow Q_\infty,\qquad Q_1\leq Q_s\leq Q_\infty.$$
--
--   At $n=0$ every rate is zero, so increasing means nondecreasing. The limits are scalar quantities, with no infinite-copy state or finite-pair optimizer asserted.
-- source:
--   Quantum Reading Capacity, arXiv:1107.3500v1, PDF p. 13, §VII Eq.(79): EPR lower-bound monotonicity and the many-pair limit

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P35

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P35

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsBarycenter tensorApply traceSize)

open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedRelativeEntropyNats binaryEntropyBits)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix coherentCoefficient)

open QAlgorithms.Papers.Independent.Support50.P20 (IsBinaryEffect)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Sec.VII, PDF p.13, (79), with theta from (33), PDF p.6: monotonicity,
both limits, and the two-sided bound. No infinite-copy state or optimizer is used. -/
theorem epr_lower_bound_monotone_limit (kappa0 n : ℝ)
    (hk : kappa0 ∈ Set.Ico (0 : ℝ) 1) (hn : 0 ≤ n) :
    (∀ s t : ℕ, 1 ≤ s → s ≤ t → eprLowerRate kappa0 s n ≤ eprLowerRate kappa0 t n) ∧
      Tendsto (fun s : ℕ => thetaFinite kappa0 s n) atTop (𝓝 (thetaLimit kappa0 n)) ∧
      Tendsto (fun s : ℕ => eprLowerRate kappa0 s n) atTop (𝓝 (eprLimitRate kappa0 n)) ∧
      ∀ s : ℕ, 1 ≤ s →
        eprLowerRate kappa0 1 n ≤ eprLowerRate kappa0 s n ∧
        eprLowerRate kappa0 s n ≤ eprLimitRate kappa0 n := by sorry

end QAlgorithms.Papers.Independent.Advance50.P35

end
