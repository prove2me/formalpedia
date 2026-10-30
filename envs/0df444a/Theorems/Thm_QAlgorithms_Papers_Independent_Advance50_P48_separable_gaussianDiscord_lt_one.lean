-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P48_separable_gaussianDiscord_lt_one
-- name    : QAlgorithms.Papers.Independent.Advance50.P48.separable_gaussianDiscord_lt_one
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:08:52.148521+00:00
-- url     : https://prove2.me/theorems/8cf4ee89-61f7-4b45-aeb5-3a9d7964025e
-- title:
--   Unnumbered: separable Gaussian discord bound and the one-nat entanglement witness
-- statement:
--   Work on two complete oscillator modes with $[q_j,p_k]=i\delta_{jk}$, vacuum covariance $I/2$, and natural logarithms, with $0\log0=0$. A state is a positive trace-class density of trace one, with no photon cutoff. Write $C_A^G(\rho)$ for the Gaussian discord obtained by measuring mode $B$ and retaining $A$: it is $S(\rho_B)-S(\rho)$ plus the infimum of the actual Born-averaged conditional von Neumann entropy over normalized Gaussian seed POVMs. Exchanging the modes defines $C_B^G$. The entropy $S$ is defined independently on the full oscillator space.
--
--   Let separability mean membership in the trace-norm closed convex hull of actual product densities. For every separable two-mode Gaussian density with finite physical covariance and arbitrary first moments,
--
--   $$C_A^G(\rho)<1,\qquad C_B^G(\rho)<1.$$
--
--   Consequently either directional discord greater than one nat implies nonseparability. There exist separable examples with positive discord below one and entangled examples with positive discord below one; no assertion is made at each specified value, in particular at zero. The paper presents the general bound as a numerically supported claim, not an analytic proof. It supplies a precise entanglement-witness target.
-- source:
--   Gaussian quantum discord, arXiv:1003.3207v2, PDF p. 3, Unnumbered: separable Gaussian discord bound and the one-nat entanglement witness

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

/-- PDF pp.1,3--4: general one-nat bound, explicitly reported as numerical
evidence in this paper. This is a precise claimed target, not an analytic-proof
attribution. Both directions above one witness actual nonseparability. -/
theorem separable_gaussianDiscord_lt_one :
    (∀ (rho : TwoKernel) (d : modePhase 2 → ℝ) (V : Matrix (modePhase 2) (modePhase 2) ℝ),
      GaussianTwo rho d V →
      (IsSeparable rho → gaussianDiscordA rho < 1 ∧ gaussianDiscordA (swapOscillators rho) < 1) ∧
      ((1 < gaussianDiscordA rho ∨ 1 < gaussianDiscordA (swapOscillators rho)) → ¬ IsSeparable rho)) ∧
    (∃ (rho : TwoKernel) (d : modePhase 2 → ℝ) (V : Matrix (modePhase 2) (modePhase 2) ℝ),
      GaussianTwo rho d V ∧ IsSeparable rho ∧ 0 < gaussianDiscordA rho ∧ gaussianDiscordA rho < 1) ∧
    (∃ (rho : TwoKernel) (d : modePhase 2 → ℝ) (V : Matrix (modePhase 2) (modePhase 2) ℝ),
      GaussianTwo rho d V ∧ ¬ IsSeparable rho ∧ 0 < gaussianDiscordA rho ∧ gaussianDiscordA rho < 1) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P48

end
