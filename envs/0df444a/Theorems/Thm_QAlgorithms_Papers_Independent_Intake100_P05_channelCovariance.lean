-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P05_channelCovariance
-- name    : QAlgorithms.Papers.Independent.Intake100.P05.channelCovariance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:45:09.227515+00:00
-- url     : https://prove2.me/theorems/6e8044c4-44e2-45b2-b9a1-834c2e08b0f0
-- title:
--   Covariance of the actual attenuator output on AB
-- statement:
--   Let $V\ge1$, $0<T\le1$, and $\chi_C\ge(1-T)/T$ be finite real parameters. Send mode $B$ of the normalized EPR preparation through the phase-insensitive attenuating line of transmittivity $T$ and input-referred noise $\chi_C$. The line is constructed as vacuum attenuation followed by independent Gaussian quadrature displacements of variance $T\chi_C-(1-T)$. No trusted detector mode is added at this stage. In the order $(q_A,p_A,q_B,p_B)$, the actual output is a centered normalized density with smooth Weyl characteristic and covariance
--
--   $$
--   \gamma_{AB}=\begin{pmatrix}VI&z\sigma\\ z\sigma&T(V+\chi_C)I\end{pmatrix},
--   \qquad z=\sqrt{T(V^2-1)},\quad I=\operatorname{diag}(1,1),\quad
--   \sigma=\operatorname{diag}(1,-1).
--   $$
--
--   The covariance is obtained from the first and second derivatives of the constructed output's characteristic function. This identifies the actual channel output with the covariance used in the security calculation; the matrix is not an assumed description of an arbitrary state.
-- source:
--   Continuous-variable quantum key distribution protocols over noisy channels, arXiv:0806.3954v2, PDF p. 3, Eq.(3)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P05

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P05

open QAlgorithms.Papers.Independent.Dependency50.P30 (thermalEntropyBits)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:0806.3954v2, PDF p.3, Eq.(3): the covariance of the actual
EPR source after the physical attenuating channel. Channel CP noise is
chiC >= (1-T)/T. The construction includes T=1 with finite additive noise,
and V=1 with zero cross covariance. Detector modes have not been added. -/
theorem channelCovariance (V T chiC : ℝ) (hV : 1 ≤ V)
    (hT : 0 < T) (hTupper : T ≤ 1) (hC : (1 - T) / T ≤ chiC) :
    IsContinuousDensityKernel volume (channelKernel V T chiC) ∧
    ContDiff ℝ 2 (kernelCharacteristic (channelKernel V T chiC)) ∧
    (∀ i, kernelMean (channelKernel V T chiC) i = 0) ∧
    kernelCovariance (channelKernel V T chiC) = abCovariance V T chiC := by sorry

end QAlgorithms.Papers.Independent.Intake100.P05

end
