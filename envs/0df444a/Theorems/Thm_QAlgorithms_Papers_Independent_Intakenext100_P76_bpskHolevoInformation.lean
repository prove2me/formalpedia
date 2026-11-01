-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P76_bpskHolevoInformation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P76.bpskHolevoInformation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:52:46.370508+00:00
-- url     : https://prove2.me/theorems/66e3a86e-c6ba-442c-b1f6-a108c51a75c8
-- title:
--   Single-letter Holevo information of the equiprobable coherent BPSK ensemble
-- statement:
--   Let $\alpha\in\mathbb C$, $N_S=|\alpha|^2$, and consider the equiprobable normalized coherent signals $|\alpha\rangle$ and $|-\alpha\rangle$ in the full oscillator Hilbert space. Form their actual average density $\bar\rho_\alpha=(|\alpha\rangle\langle\alpha|+|-\alpha\rangle\langle-\alpha|)/2$. Their overlap is real and positive, $\langle-\alpha|\alpha\rangle=e^{-2N_S}$, and their single-letter Holevo information is
--
--   $$
--   \chi=H(\bar\rho_\alpha)=h_2\!\left(\frac{1-\langle-\alpha|\alpha\rangle}{2}\right)=h_2\!\left(\frac{1-e^{-2N_S}}{2}\right)\ \text{bits per mode}.
--   $$
--
--   Here $h_2(t)=-t\log_2t-(1-t)\log_2(1-t)$ with $0\log 0=0$. Since both signals are pure, their individual entropies vanish. At $\alpha=0$, the formula gives zero.
-- source:
--   Second-order coding rates for pure-loss bosonic channels, arXiv:1408.5328v3, PDF p. 13, §6.2, (6.14)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P76

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P76

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.13, (6.14): entropy of the actual equiprobable coherent-state mixture.
Pure signals have zero entropy, so this entropy is their single-letter Holevo
information. It is not defined to equal the scalar formula. Includes alpha=0. -/
theorem bpskHolevoInformation (alpha : ℂ) :
    coefficientInner (coherentCoefficient (-alpha)) (coherentCoefficient alpha) =
      (Real.exp (-2 * Complex.normSq alpha) : ℂ) ∧
    kernelEntropyBits (bpskAverage alpha) =
      ENNReal.ofReal (QAlgorithms.binEntropy2
        ((1 - (coefficientInner (coherentCoefficient (-alpha))
          (coherentCoefficient alpha)).re) / 2)) ∧
    kernelEntropyBits (bpskAverage alpha) =
      ENNReal.ofReal (bpskHolevoBits (Complex.normSq alpha)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P76

end
