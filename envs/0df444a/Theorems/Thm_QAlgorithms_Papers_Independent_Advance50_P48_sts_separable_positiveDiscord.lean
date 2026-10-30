-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P48_sts_separable_positiveDiscord
-- name    : QAlgorithms.Papers.Independent.Advance50.P48.sts_separable_positiveDiscord
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:08:08.799646+00:00
-- url     : https://prove2.me/theorems/b07d7389-6a2f-484a-bdb6-1ad954cf4b26
-- title:
--   Unnumbered: separable STS with positive Gaussian discord exist
-- statement:
--   Work on two complete oscillator modes with $[q_j,p_k]=i\delta_{jk}$, vacuum covariance $I/2$, and natural logarithms, with $0\log0=0$. A state is a positive trace-class density of trace one, with no photon cutoff. Write $C_A^G(\rho)$ for the Gaussian discord obtained by measuring mode $B$ and retaining $A$: it is $S(\rho_B)-S(\rho)$ plus the infimum of the actual Born-averaged conditional von Neumann entropy over normalized Gaussian seed POVMs. Exchanging the modes defines $C_B^G$. The entropy $S$ is defined independently on the full oscillator space.
--
--   Let $N_1,N_2,r\ge0$ be finite real numbers, let $\nu(N)$ have number probabilities $N^k/(1+N)^{k+1}$, and let $\rho=S(r)[\nu(N_1)\otimes\nu(N_2)]S(r)^\dagger$, where $S(r)=\exp[r(a^\dagger b^\dagger-ab)]$. Put $N_r=\sinh^2 r$.
--
--   With separability defined by the trace-norm closed convex hull of product densities, the STS threshold gives
--
--   $$N_r\le\frac{N_1N_2}{1+N_1+N_2}\ \Longrightarrow\ \rho\text{ is separable}.$$
--
--   If also $N_r>0$, both directional Gaussian discords are strictly positive. Such finite states with $r>0$ exist. The unsqueezed product boundary remains included in the separability assertion; it is excluded only from the positive-discord conclusion. Thus separability does not force Gaussian discord to vanish.
-- source:
--   Gaussian quantum discord, arXiv:1003.3207v2, PDF p. 3, Unnumbered: separable STS with positive Gaussian discord exist

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

/-- PDF p.3: the STS separability threshold includes equality; nonzero
squeezing in the separable regime gives positive discord, and such states exist. -/
theorem sts_separable_positiveDiscord :
    (∀ N1 N2 r : ℝ, 0 ≤ N1 → 0 ≤ N2 → 0 ≤ r →
      squeezingPhotons r ≤ N1*N2/(1+N1+N2) →
      IsSeparable (sts N1 N2 r) ∧
      (0 < squeezingPhotons r → 0 < gaussianDiscordA (sts N1 N2 r) ∧
        0 < gaussianDiscordA (swapOscillators (sts N1 N2 r)))) ∧
    (∃ N1 N2 r : ℝ, 0 ≤ N1 ∧ 0 ≤ N2 ∧ 0 < r ∧
      IsSeparable (sts N1 N2 r) ∧ 0 < gaussianDiscordA (sts N1 N2 r)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P48

end
