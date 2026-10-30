-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P48_gaussianDiscord_zero_iff_product
-- name    : QAlgorithms.Papers.Independent.Advance50.P48.gaussianDiscord_zero_iff_product
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:07:21.18875+00:00
-- url     : https://prove2.me/theorems/c29e4607-d410-4274-b3a9-406f6435670e
-- title:
--   Unnumbered: zero Gaussian discord iff product; STS criterion Nr=0
-- statement:
--   Work on two complete oscillator modes with $[q_j,p_k]=i\delta_{jk}$, vacuum covariance $I/2$, and natural logarithms, with $0\log0=0$. A state is a positive trace-class density of trace one, with no photon cutoff. Write $C_A^G(\rho)$ for the Gaussian discord obtained by measuring mode $B$ and retaining $A$: it is $S(\rho_B)-S(\rho)$ plus the infimum of the actual Born-averaged conditional von Neumann entropy over normalized Gaussian seed POVMs. Exchanging the modes defines $C_B^G$. The entropy $S$ is defined independently on the full oscillator space.
--
--   For every actual two-mode Gaussian density $\rho$ with finite physical covariance $\sigma=\begin{pmatrix}A&C\\C^T&B\end{pmatrix}$ and arbitrary first moments,
--
--   $$C_A^G(\rho)=0\ \Longleftrightarrow\ C_B^G(\rho)=0\ \Longleftrightarrow\ \rho=\rho_A\otimes\rho_B\ \Longleftrightarrow\ C=0.$$
--
--   Both discord directions are nonnegative. For squeezed thermal states with finite $N_1,N_2,r\ge0$, vanishing in either direction is equivalent to $N_r=\sinh^2r=0$; if $r>0$, both directions are strictly positive. This is a density product equivalence and does not invent a measure for the phrase almost all.
-- source:
--   Gaussian quantum discord, arXiv:1003.3207v2, PDF p. 3, Unnumbered: zero Gaussian discord iff product; STS criterion Nr=0

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

/-- PDF pp.1,3: Gaussian zero discord is equivalent to the ACTUAL product of
its density marginals, not a covariance-only surrogate. The STS zero set is Nr=0. -/
theorem gaussianDiscord_zero_iff_product :
    (∀ (rho : TwoKernel) (d : modePhase 2 → ℝ) (V : Matrix (modePhase 2) (modePhase 2) ℝ),
      GaussianTwo rho d V →
      (gaussianDiscordA rho = 0 ↔ rho = productCoeff (partialRight rho) (partialLeft rho)) ∧
      (gaussianDiscordA (swapOscillators rho) = 0 ↔ rho = productCoeff (partialRight rho) (partialLeft rho)) ∧
      (rho = productCoeff (partialRight rho) (partialLeft rho) ↔ covarianceModeBlock V 0 1 = 0) ∧
      0 ≤ gaussianDiscordA rho ∧ 0 ≤ gaussianDiscordA (swapOscillators rho)) ∧
    (∀ N1 N2 r : ℝ, 0 ≤ N1 → 0 ≤ N2 → 0 ≤ r →
      (gaussianDiscordA (sts N1 N2 r) = 0 ↔ squeezingPhotons r = 0) ∧
      (gaussianDiscordA (swapOscillators (sts N1 N2 r)) = 0 ↔ squeezingPhotons r = 0) ∧
      (0 < r → 0 < gaussianDiscordA (sts N1 N2 r) ∧ 0 < gaussianDiscordA (swapOscillators (sts N1 N2 r)))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P48

end
