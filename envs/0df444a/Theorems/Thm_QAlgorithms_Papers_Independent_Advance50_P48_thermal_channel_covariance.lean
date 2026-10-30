-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P48_thermal_channel_covariance
-- name    : QAlgorithms.Papers.Independent.Advance50.P48.thermal_channel_covariance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:13:47.150302+00:00
-- url     : https://prove2.me/theorems/a15e3180-c58b-4ebb-adf4-05a69d5bff90
-- title:
--   Unnumbered: covariance evolution in independent thermal reservoirs
-- statement:
--   Work on two complete oscillator modes with $[q_j,p_k]=i\delta_{jk}$, vacuum covariance $I/2$, and natural logarithms, with $0\log0=0$. A state is a positive trace-class density of trace one, with no photon cutoff. Write $C_A^G(\rho)$ for the Gaussian discord obtained by measuring mode $B$ and retaining $A$: it is $S(\rho_B)-S(\rho)$ plus the infimum of the actual Born-averaged conditional von Neumann entropy over normalized Gaussian seed POVMs. Exchanging the modes defines $C_B^G$. The entropy $S$ is defined independently on the full oscillator space.
--
--   Let $\rho$ be any actual two-mode Gaussian density, with arbitrary first moments and finite physical covariance $\sigma$. Let $\Gamma_1,\Gamma_2,M_1,M_2,t\ge0$ be finite. The independent thermal attenuators are specified as trace-class CPTP maps by their all-density Weyl characteristic law, with amplitude damping $e^{-\Gamma_jt/2}$ and thermal noise $M_j+1/2$. The output is Gaussian, its first moments are damped by those amplitudes, and
--
--   $$\sigma_t=G_t^{1/2}\sigma G_t^{1/2}+(I-G_t)\sigma_\infty,$$
--
--   where $G_t=\operatorname{diag}(e^{-\Gamma_1t}I_2,e^{-\Gamma_2t}I_2)$ and $\sigma_\infty=\operatorname{diag}((M_1+1/2)I_2,(M_2+1/2)I_2)$. In standard form, $a_t=ae^{-\Gamma_1t}+(1-e^{-\Gamma_1t})(M_1+1/2)$, $b_t=be^{-\Gamma_2t}+(1-e^{-\Gamma_2t})(M_2+1/2)$, and each $c_i$ is multiplied by $e^{-(\Gamma_1+\Gamma_2)t/2}$. This includes zero damping and time zero. It makes no unconditional marginal-growth or convergence assertion.
-- source:
--   Gaussian quantum discord, arXiv:1003.3207v2, PDF p. 4, Unnumbered: covariance evolution in independent thermal reservoirs

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

/-- PDF p.4: independent physical thermal reservoirs preserve standard form
and give exactly the displayed covariance map. Zero damping and t=0 are included;
no unconditional marginal growth or undamped convergence is asserted. -/
theorem thermal_channel_covariance (Phi : TwoKernel → TwoKernel)
    (g1 g2 M1 M2 t : ℝ)
    (hg1 : 0 ≤ g1) (hg2 : 0 ≤ g2) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (ht : 0 ≤ t)
    (hPhi : ThermalEvolution Phi g1 g2 M1 M2 t)
    (rho : TwoKernel) (d : modePhase 2 → ℝ) (V : Matrix (modePhase 2) (modePhase 2) ℝ)
    (hrho : GaussianTwo rho d V) :
    GaussianTwo (Phi rho) (dampedArgument g1 g2 t d) (attenuatedCovariance V g1 g2 M1 M2 t) ∧
    (∀ a b c1 c2 : ℝ, V = twoModeStandard a b c1 c2 →
      attenuatedCovariance V g1 g2 M1 M2 t =
      twoModeStandard (a * Real.exp (-g1*t) + (1-Real.exp (-g1*t))*(M1+1/2))
        (b * Real.exp (-g2*t) + (1-Real.exp (-g2*t))*(M2+1/2))
        (c1 * Real.exp (-(g1+g2)*t/2)) (c2 * Real.exp (-(g1+g2)*t/2))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P48

end
