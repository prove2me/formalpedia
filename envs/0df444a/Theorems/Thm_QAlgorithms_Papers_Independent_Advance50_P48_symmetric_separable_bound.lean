-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P48_symmetric_separable_bound
-- name    : QAlgorithms.Papers.Independent.Advance50.P48.symmetric_separable_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:12:28.46797+00:00
-- url     : https://prove2.me/theorems/18081556-0013-4a31-9a37-1b6d623a334f
-- title:
--   Unnumbered: symmetric separable STS bound
-- statement:
--   Work on two complete oscillator modes with $[q_j,p_k]=i\delta_{jk}$, vacuum covariance $I/2$, and natural logarithms, with $0\log0=0$. A state is a positive trace-class density of trace one, with no photon cutoff. Write $C_A^G(\rho)$ for the Gaussian discord obtained by measuring mode $B$ and retaining $A$: it is $S(\rho_B)-S(\rho)$ plus the infimum of the actual Born-averaged conditional von Neumann entropy over normalized Gaussian seed POVMs. Exchanging the modes defines $C_B^G$. The entropy $S$ is defined independently on the full oscillator space.
--
--   Let $N,r\ge0$ be finite and let $\rho=S(r)[\nu(N)\otimes\nu(N)]S(r)^\dagger$ be separable in the trace-norm closed convex-hull sense. Then
--
--   $$C_A^G(\rho)=C_B^G(\rho)<2\log2-1,$$
--
--   and hence the non-strict inequality printed on page 3 holds as well. The strict finite-state statement is printed in the conclusion on page 4; the constant is a limiting value along the fixed-PT family, not a claimed finite maximizer. This distinguishes a bound from its attainment.
-- source:
--   Gaussian quantum discord, arXiv:1003.3207v2, PDF p. 3, Unnumbered: symmetric separable STS bound

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

/-- PDF pp.3--4: the finite symmetric separable bound is strict on p.4,
with the non-strict p.3 statement retained as a corollary clause. -/
theorem symmetric_separable_bound (N r : ℝ) (hN : 0 ≤ N) (hr : 0 ≤ r)
    (hsep : IsSeparable (sts N N r)) :
    gaussianDiscordA (swapOscillators (sts N N r)) = gaussianDiscordA (sts N N r) ∧
    gaussianDiscordA (sts N N r) < 2*Real.log 2 - 1 ∧
    gaussianDiscordA (sts N N r) ≤ 2*Real.log 2 - 1 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P48

end
