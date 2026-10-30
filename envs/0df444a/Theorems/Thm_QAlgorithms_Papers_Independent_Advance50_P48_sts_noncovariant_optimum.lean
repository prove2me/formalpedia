-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P48_sts_noncovariant_optimum
-- name    : QAlgorithms.Papers.Independent.Advance50.P48.sts_noncovariant_optimum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:06:22.779935+00:00
-- url     : https://prove2.me/theorems/67618361-3986-452f-9912-2b2b2d45fdc3
-- title:
--   Unnumbered: the STS optimum persists for normalized noncovariant Gaussian seed POVMs
-- statement:
--   Work on two complete oscillator modes with $[q_j,p_k]=i\delta_{jk}$, vacuum covariance $I/2$, and natural logarithms, with $0\log0=0$. A state is a positive trace-class density of trace one, with no photon cutoff. Write $C_A^G(\rho)$ for the Gaussian discord obtained by measuring mode $B$ and retaining $A$: it is $S(\rho_B)-S(\rho)$ plus the infimum of the actual Born-averaged conditional von Neumann entropy over normalized Gaussian seed POVMs. Exchanging the modes defines $C_B^G$. The entropy $S$ is defined independently on the full oscillator space.
--
--   Let $N_1,N_2,r\ge0$ be finite real numbers, let $\nu(N)$ have number probabilities $N^k/(1+N)^{k+1}$, and let $\rho=S(r)[\nu(N_1)\otimes\nu(N_2)]S(r)^\dagger$, where $S(r)=\exp[r(a^\dagger b^\dagger-ab)]$. Put $N_r=\sinh^2 r$.
--
--   Allow measurable outcome-dependent centered Gaussian seeds, displaced by the outcome, with their actual nonnegative weights and reference measure. Require weak POVM normalization against every finite superposition of number states. If $E_z$ is the resulting effect density, let $p(z)=\operatorname{Tr}[\rho(I\otimes E_z)]$ and let $\rho_{A|z}$ be the normalized partial trace on $p(z)>0$. Write $H_{\rm het}$ for the actual average conditional entropy of the coherent-state POVM. Then
--
--   $$\int S(\rho_{A|z})\,dp(z)\ge H_{\rm het},\qquad \inf_{\text{normalized variable-seed POVMs}}\int S(\rho_{A|z})\,dp(z)=H_{\rm het}.$$
--
--   The Born law is a probability law, equality is attained, and the same lower bound holds for any limit of finite-seed average entropies, including homodyne limits. The opposite direction has the corresponding lower bound after exchanging the modes. This is an assertion about normalized Gaussian measurements, without an all-POVM claim.
-- source:
--   Gaussian quantum discord, arXiv:1003.3207v2, PDF p. 3, Unnumbered: the STS optimum persists for normalized noncovariant Gaussian seed POVMs

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P48

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsDensity IsTraceClassChannel IsSeparable productCoeff)

open QAlgorithms.Papers.Independent.Dependency50.P39
  (displacementMatrix coherentMeasure coherentCoefficient)

open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)

open QAlgorithms.Papers.Independent.Frontier30.P04 (modePhase twoModeStandard conditionalCovariance)

open QAlgorithms.Papers.Independent.Frontier30.P14 (partialRight partialLeft)

open QAlgorithms.Papers.Independent.Claimed50.P30 (canonicalOmega)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g thermalProbability)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.2--3: enlarging to weakly normalized variable-seed Gaussian POVMs
preserves the attained heterodyne value. Actual Born normalization is essential. -/
theorem sts_noncovariant_optimum (N1 N2 r : ℝ) (hN1 : 0 ≤ N1) (hN2 : 0 ≤ N2) (hr : 0 ≤ r) :
    (∀ M : NoncovariantMeasurement,
      IsProbabilityMeasure (variableLaw (sts N1 N2 r) M) ∧
      heterodyneAverage (sts N1 N2 r) ≤ variableAverage (sts N1 N2 r) M) ∧
    (∃ M : NoncovariantMeasurement,
      variableAverage (sts N1 N2 r) M = heterodyneAverage (sts N1 N2 r)) ∧
    (⨅ M : NoncovariantMeasurement, variableAverage (sts N1 N2 r) M) =
      heterodyneAverage (sts N1 N2 r) ∧
    (∀ (seeds : ℕ → GaussianSeed) (v : ℝ≥0∞),
      Tendsto (fun n => seedAverage (sts N1 N2 r) (seeds n)) atTop (𝓝 v) →
      heterodyneAverage (sts N1 N2 r) ≤ v) ∧
    (∀ M : NoncovariantMeasurement,
      heterodyneAverage (swapOscillators (sts N1 N2 r)) ≤ variableAverage (swapOscillators (sts N1 N2 r)) M) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P48

end
