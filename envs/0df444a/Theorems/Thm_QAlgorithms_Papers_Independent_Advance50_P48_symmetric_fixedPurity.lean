-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P48_symmetric_fixedPurity
-- name    : QAlgorithms.Papers.Independent.Advance50.P48.symmetric_fixedPurity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:09:41.735387+00:00
-- url     : https://prove2.me/theorems/a876c89f-87b9-47ba-b59b-2c70730da4e2
-- title:
--   Unnumbered: symmetric STS discord grows with entanglement at fixed purity
-- statement:
--   Work on two complete oscillator modes with $[q_j,p_k]=i\delta_{jk}$, vacuum covariance $I/2$, and natural logarithms, with $0\log0=0$. A state is a positive trace-class density of trace one, with no photon cutoff. Write $C_A^G(\rho)$ for the Gaussian discord obtained by measuring mode $B$ and retaining $A$: it is $S(\rho_B)-S(\rho)$ plus the infimum of the actual Born-averaged conditional von Neumann entropy over normalized Gaussian seed POVMs. Exchanging the modes defines $C_B^G$. The entropy $S$ is defined independently on the full oscillator space.
--
--   Fix a finite $N\ge0$ and write $\rho_r=S(r)[\nu(N)\otimes\nu(N)]S(r)^\dagger$ for canonical $r\ge0$. For $0\le r_1<r_2$,
--
--   $$\operatorname{Tr}(\rho_{r_1}^2)=\operatorname{Tr}(\rho_{r_2}^2)=(1+2N)^{-2},\qquad C_A^G(\rho_{r_1})<C_A^G(\rho_{r_2}).$$
--
--   Equivalently discord decreases with the PT parameter $t=e^{-2r}(1+2N)/2$ at fixed purity. On $t<1/2$ this orders the entangled symmetric family by entanglement. The statement uses the explicit squeezing order, not an invented entanglement measure.
-- source:
--   Gaussian quantum discord, arXiv:1003.3207v2, PDF p. 3, Unnumbered: symmetric STS discord grows with entanglement at fixed purity

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

/-- PDF p.3: at fixed symmetric thermal input (hence fixed ACTUAL global
purity), Gaussian discord strictly grows with the canonical squeezing parameter.
This is the source's explicit entanglement-order parameter; no entanglement
measure is redefined to be discord. -/
theorem symmetric_fixedPurity (N r1 r2 : ℝ) (hN : 0 ≤ N)
    (hr1 : 0 ≤ r1) (hrr : r1 < r2) :
    tracePurity (sts N N r1) = ((1 + 2*N)^2)⁻¹ ∧
    tracePurity (sts N N r2) = ((1 + 2*N)^2)⁻¹ ∧
    gaussianDiscordA (sts N N r1) < gaussianDiscordA (sts N N r2) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P48

end
