-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P37_tmsCorrelationMaximum
-- name    : QAlgorithms.Papers.Independent.Advance50.P37.tmsCorrelationMaximum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:41:13.645602+00:00
-- url     : https://prove2.me/theorems/a0e918de-883d-4a63-a517-5c558717d52d
-- title:
--   Maximum physical correlation in the equal-variance covariance family
-- statement:
--   Let $V_A\ge0$. Consider every centered, normalized two-mode bosonic density $\rho$ with finite second moments and shot-noise covariance
--
--   $$
--   \Gamma(V_A,Z)=\begin{pmatrix}(V_A+1)I_2&Z\operatorname{diag}(1,-1)\\Z\operatorname{diag}(1,-1)&(V_A+1)I_2\end{pmatrix}.
--   $$
--
--   Then $Z\le\sqrt{V_A^2+2V_A}$. Moreover, there is $r\ge0$ with $\cosh(2r)=V_A+1$ for which the actual two-mode squeezed-vacuum density, with Fock amplitudes $\tanh(r)^n/\cosh(r)$ on $|n,n\rangle$, is normalized, centered Gaussian and has covariance
--
--   $$
--   \Gamma\!\left(V_A,\sqrt{V_A^2+2V_A}\right).
--   $$
--
--   Thus the upper bound is attained. Competing states need not be Gaussian and their correlations are not assumed nonnegative. The boundary $V_A=0$ is included, with vacuum attainment at $r=0$.
--
--   The formal covariance uses the accepted full anticommutator at $[Q,P]=i$, numerically equal to the source's shot-noise covariance.
-- source:
--   Long distance quantum key distribution with continuous variables, arXiv:1005.0328v3, PDF p. 6, Section 3: maximal physical equal-variance correlation attained by a two-mode squeezed state

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P37

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P37

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Gap48.P26 (totalPhotons)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsDensity IsBarycenter IsTraceClassChannel productCoeff)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (FockIndex DensityKernel Cov standardFormCovariance vacuumKernel productWeyl weylArgument)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (unitaryCoeff conjugateKernel boundedUnitaryConjugation partialRight)

open QAlgorithms.Papers.Independent.Support50.P14 (CompleteMoments GaussianAt)

open QAlgorithms.Papers.Independent.Renew46.P39 (squeezedVacuum)

open QAlgorithms.Papers.Independent.Renew46.P41
  (coherentProductCoefficient NormalizedCoherent)

/-- PDF p.6: maximum in the centered equal-variance standard-form family,
with attainment by an actual two-mode squeezed state. V_A=0 is included;
no Gaussianity or nonnegative-Z assumption is imposed on a competitor. -/
theorem tmsCorrelationMaximum (modulationVariance : ℝ)
    (hvariance : 0 ≤ modulationVariance) :
    (∀ (rho : DensityKernel 2) (Z : ℝ), IsDensity rho →
      CompleteMoments rho 0 (standardFormCovariance
        (modulationVariance + 1) (modulationVariance + 1) Z (-Z)) →
      Z ≤ Real.sqrt (modulationVariance ^ 2 + 2 * modulationVariance)) ∧
    ∃ r : ℝ, 0 ≤ r ∧ Real.cosh (2 * r) = modulationVariance + 1 ∧
      IsDensity (squeezedVacuum r) ∧
      GaussianAt (squeezedVacuum r) 0
        (standardFormCovariance (modulationVariance + 1) (modulationVariance + 1)
          (Real.sqrt (modulationVariance ^ 2 + 2 * modulationVariance))
          (-Real.sqrt (modulationVariance ^ 2 + 2 * modulationVariance))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P37

end
