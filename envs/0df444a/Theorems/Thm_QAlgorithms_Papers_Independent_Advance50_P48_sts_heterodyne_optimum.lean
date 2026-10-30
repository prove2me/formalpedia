-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P48_sts_heterodyne_optimum
-- name    : QAlgorithms.Papers.Independent.Advance50.P48.sts_heterodyne_optimum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:05:35.00809+00:00
-- url     : https://prove2.me/theorems/766762dc-9391-465f-b3aa-ac839567853f
-- title:
--   Unnumbered: heterodyne attains the Gaussian measurement optimum for every STS
-- statement:
--   Work on two complete oscillator modes with $[q_j,p_k]=i\delta_{jk}$, vacuum covariance $I/2$, and natural logarithms, with $0\log0=0$. A state is a positive trace-class density of trace one, with no photon cutoff. Write $C_A^G(\rho)$ for the Gaussian discord obtained by measuring mode $B$ and retaining $A$: it is $S(\rho_B)-S(\rho)$ plus the infimum of the actual Born-averaged conditional von Neumann entropy over normalized Gaussian seed POVMs. Exchanging the modes defines $C_B^G$. The entropy $S$ is defined independently on the full oscillator space.
--
--   Let $N_1,N_2,r\ge0$ be finite real numbers, let $\nu(N)$ have number probabilities $N^k/(1+N)^{k+1}$, and let $\rho=S(r)[\nu(N_1)\otimes\nu(N_2)]S(r)^\dagger$, where $S(r)=\exp[r(a^\dagger b^\dagger-ab)]$. Put $N_r=\sinh^2 r$.
--
--   Put $a=N_r+\tfrac12+N_1(1+N_r)+N_2N_r$, $b=N_r+\tfrac12+N_2(1+N_r)+N_1N_r$, $c=(1+N_1+N_2)\sqrt{N_r(1+N_r)}$, and $h(x)=(x+\tfrac12)\log(x+\tfrac12)-(x-\tfrac12)\log(x-\tfrac12)$. Heterodyne detection on $B$, with vacuum seed covariance $I/2$, attains the Gaussian conditional-entropy minimum:
--
--   $$\min_M\int S(\rho_{A|z})\,dp_M(z)=h\!\left(a-\frac{c^2}{b+1/2}\right).$$
--
--   Its conditional entropy has this value almost everywhere under its actual Born law. A normalized vacuum seed exists and realizes the optimum; no uniqueness or strict advantage is asserted. The reverse direction has value $h(b-c^2/(a+1/2))$. Thus the source asserts attainment, including product and pure STS.
-- source:
--   Gaussian quantum discord, arXiv:1003.3207v2, PDF p. 2, Unnumbered: heterodyne attains the Gaussian measurement optimum for every STS

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

/-- PDF pp.2--3: heterodyne ATTAINS the Gaussian optimum, including product
and pure STS. The printed word identity means I/2, fixed by alpha=beta=1/2. -/
theorem sts_heterodyne_optimum (N1 N2 r : ℝ) (hN1 : 0 ≤ N1) (hN2 : 0 ≤ N2) (hr : 0 ≤ r) :
    heterodyneAverage (sts N1 N2 r) = gaussianConditionalInf (sts N1 N2 r) ∧
    (∃ s : GaussianSeed, s.density = oneModeVacuum ∧
      s.covariance = (1/2 : ℝ) • (1 : Matrix (modePhase 1) (modePhase 1) ℝ) ∧
      seedAverage (sts N1 N2 r) s = gaussianConditionalInf (sts N1 N2 r)) ∧
    (∀ s : GaussianSeed, heterodyneAverage (sts N1 N2 r) ≤ seedAverage (sts N1 N2 r) s) ∧
    heterodyneAverage (sts N1 N2 r) = ENNReal.ofReal
      (halfUnitEntropy (stsA N1 N2 r - (stsC N1 N2 r)^2 / (stsB N1 N2 r + 1/2))) ∧
    (∀ᵐ z ∂(coherentMeasure.withDensity
      (fun z => ENNReal.ofReal (bornDensity (sts N1 N2 r) (heterodyneEffect z)))),
      extendedEntropyNats (posteriorDensity (sts N1 N2 r) (heterodyneEffect z)) =
        ENNReal.ofReal (halfUnitEntropy (stsA N1 N2 r - (stsC N1 N2 r)^2 / (stsB N1 N2 r + 1/2)))) ∧
    heterodyneAverage (swapOscillators (sts N1 N2 r)) =
      gaussianConditionalInf (swapOscillators (sts N1 N2 r)) ∧
    heterodyneAverage (swapOscillators (sts N1 N2 r)) = ENNReal.ofReal
      (halfUnitEntropy (stsB N1 N2 r - (stsC N1 N2 r)^2 / (stsA N1 N2 r + 1/2))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P48

end
