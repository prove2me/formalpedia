-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P17_heat_gaussification_relative_entropy
-- name    : QAlgorithms.Papers.Independent.Next46.P17.heat_gaussification_relative_entropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:24:16.641392+00:00
-- url     : https://prove2.me/theorems/f6da7d75-1ef0-48be-9575-82da80cc9f38
-- title:
--   Equation (64): heat gaussification relative entropy
-- statement:
--   Let $n\geq1$ and let $\rho$ be a normalized full $n$-mode state with finite first and second quadrature moments. Let $\mathcal N_t$ denote canonical diffusion. For a finite-moment state $\sigma$, write $\sigma^G$ for the Gaussian state with exactly the same first moments and twice-symmetrized centered covariance. Then, for relative entropy in nats,
--
--   $$
--   \lim_{t\to\infty}D\bigl(\mathcal N_t\rho\Vert(\mathcal N_t\rho)^G\bigr)=0.
--   $$
--
--   The Gaussian reference is computed by Weyl inversion from the actual quadrature moments of the evolving state. Convergence is in relative entropy.
-- source:
--   The entropy power inequality for quantum systems, arXiv:1205.3409v2, PDF p. 9, Equation (64)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P17

noncomputable section

open Filter MeasureTheory

open scoped ENNReal BigOperators Topology

namespace QAlgorithms.Papers.Independent.Next46.P17

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel productCoeff tensorApply)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats)

open QAlgorithms.Papers.Independent.Claimed50.P19 (productWeyl FiniteMeanEnergy PhysicalCovariance Cov FockIndex covarianceCharacteristicValue)

open QAlgorithms.Papers.Independent.Frontier30.P08 (interleavedSymplecticForm)

/-- PDF p.9, (64): relative-entropy convergence to the moment-matched Gaussian,
with finite quadrature moments expressed as finite mean number energy.
Relative entropy remains extended nonnegative; no infinity-minus-infinity is used. -/
theorem heat_gaussification_relative_entropy {n : ℕ} (hn : 0 < n)
    (rho : State (FockIndex n)) (hEnergy : FiniteMeanEnergy rho.coefficients) :
    Tendsto (fun t : ℝ => extendedRelativeEntropyNats (diffusionChannel t rho.coefficients)
      (gaussification (diffusionChannel t rho.coefficients))) atTop (𝓝 0) := by sorry

end QAlgorithms.Papers.Independent.Next46.P17

end
