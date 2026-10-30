-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P48_gaussianDiscord_variational
-- name    : QAlgorithms.Papers.Independent.Advance50.P48.gaussianDiscord_variational
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:03:24.729839+00:00
-- url     : https://prove2.me/theorems/e171e4b5-f823-4903-bc40-a3e350b59525
-- title:
--   Eq. (1): general covariance variational formula for Gaussian discord
-- statement:
--   Work on two complete oscillator modes with $[q_j,p_k]=i\delta_{jk}$, vacuum covariance $I/2$, and natural logarithms, with $0\log0=0$. A state is a positive trace-class density of trace one, with no photon cutoff. Write $C_A^G(\rho)$ for the Gaussian discord obtained by measuring mode $B$ and retaining $A$: it is $S(\rho_B)-S(\rho)$ plus the infimum of the actual Born-averaged conditional von Neumann entropy over normalized Gaussian seed POVMs. Exchanging the modes defines $C_B^G$. The entropy $S$ is defined independently on the full oscillator space.
--
--   Let $\rho$ be any two-mode Gaussian density, with arbitrary first moments and finite physical symmetric covariance $\sigma=\begin{pmatrix}A&C\\C^T&B\end{pmatrix}$. Physical means $\sigma+i\Omega/2\succeq0$, where $\Omega$ is the direct sum of the two canonical $\begin{psmallmatrix}0&1\\-1&0\end{psmallmatrix}$ blocks. Set $I_1=\det A$, $I_2=\det B$, $I_3=\det C$, $I_4=\det\sigma$, $\Delta=I_1+I_2+2I_3$, and $d_\pm=\sqrt{(\Delta\pm\sqrt{\Delta^2-4I_4})/2}$. Let $h(x)=(x+\tfrac12)\log(x+\tfrac12)-(x-\tfrac12)\log(x-\tfrac12)$. Then
--
--   $$C_A^G(\rho)=h(\sqrt{\det B})-h(d_-)-h(d_+)+\inf_{M+i\Omega_1/2\succeq0}h\!\left(\sqrt{\det[A-C(B+M)^{-1}C^T]}\right).$$
--
--   The infimum ranges over finite real symmetric physical one-mode seed covariances. It equals the actual Gaussian measurement conditional-entropy infimum. All three state entropies and this infimum are finite; actual seed Born laws are probability laws and the conditional kernels are normalized densities almost everywhere. Gaussian extractable information is $J_A^G=h(\sqrt{\det A})$ minus the same infimum. The opposite discord direction exchanges the modes. Finite squeezed seeds include homodyne values as limits. This identifies the physical variational problem without defining entropy or discord by a covariance formula.
-- source:
--   Gaussian quantum discord, arXiv:1003.3207v2, PDF p. 2, Eq. (1): general covariance variational formula for Gaussian discord

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

/-- PDF p.2, Eq.(1): independent Gaussian measurement optimization equals the
covariance variational formula. Gaussian entropy finiteness, normalized Born
laws and posterior density validity are conclusions, not hypotheses. Printed
h(sqrt(sigma_P)) is read as h(sqrt(det sigma_P)), as its entropy meaning requires. -/
theorem gaussianDiscord_variational (rho : TwoKernel) (d : modePhase 2 → ℝ)
    (V : Matrix (modePhase 2) (modePhase 2) ℝ) (hg : GaussianTwo rho d V) :
    extendedEntropyNats rho < ⊤ ∧
    extendedEntropyNats (partialRight rho) < ⊤ ∧
    extendedEntropyNats (partialLeft rho) < ⊤ ∧
    gaussianConditionalInf rho < ⊤ ∧ covarianceInf V < ⊤ ∧
    extendedEntropyNats rho = ENNReal.ofReal (halfUnitEntropy (symplecticMinus V) + halfUnitEntropy (symplecticPlus V)) ∧
    extendedEntropyNats (partialRight rho) = ENNReal.ofReal (halfUnitEntropy (Real.sqrt (covarianceInvariant V 0))) ∧
    extendedEntropyNats (partialLeft rho) = ENNReal.ofReal (halfUnitEntropy (Real.sqrt (covarianceInvariant V 1))) ∧
    (∀ s : GaussianSeed, IsProbabilityMeasure (seedLaw rho s) ∧
      (∀ᵐ z ∂seedLaw rho s, IsDensity (posteriorDensity rho (seedEffect s z)) ∧
        extendedEntropyNats (posteriorDensity rho (seedEffect s z)) =
          ENNReal.ofReal (halfUnitEntropy (Real.sqrt ((gaussianSchurCovariance V s.covariance).det)))) ∧
      seedAverage rho s = ENNReal.ofReal (halfUnitEntropy (Real.sqrt ((gaussianSchurCovariance V s.covariance).det)))) ∧
    gaussianConditionalInf rho = covarianceInf V ∧
    gaussianDiscordA rho = halfUnitEntropy (Real.sqrt (covarianceInvariant V 1)) - halfUnitEntropy (symplecticMinus V) -
      halfUnitEntropy (symplecticPlus V) + (covarianceInf V).toReal ∧
    gaussianClassicalCorrelationA rho = halfUnitEntropy (Real.sqrt (covarianceInvariant V 0)) - (covarianceInf V).toReal ∧
    gaussianDiscordA (swapOscillators rho) = halfUnitEntropy (Real.sqrt (covarianceInvariant V 0)) - halfUnitEntropy (symplecticMinus V) -
      halfUnitEntropy (symplecticPlus V) +
      (covarianceInf (fun i j => V ((if i.1 = 0 then 1 else 0), i.2) ((if j.1 = 0 then 1 else 0), j.2))).toReal := by sorry

end QAlgorithms.Papers.Independent.Advance50.P48

end
