-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P20_complementaryPhotonChannels
-- name    : QAlgorithms.Papers.Independent.Advance50.P20.complementaryPhotonChannels
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:30:19.412318+00:00
-- url     : https://prove2.me/theorems/4182fb2f-2f54-48d5-bdd0-0641ac1a95b8
-- title:
--   Complementary photon-added amplifier and attenuator channels
-- statement:
--   Let $\mathcal H=\ell^2(\mathbb N)$, with normalized number states $|j\rangle$, and let $n\in\mathbb N$ be the environment photon number. Write $A(\kappa;n)$, $B(\kappa;n)$ and $C(\kappa;n)$ for the canonical amplifier, attenuator and phase-conjugator channels, respectively. Their amplitude domains are $\kappa\ge1$, $0\le\kappa\le1$ and $\kappa\ge0$. Each channel is defined by its specified two-mode unitary, the product environment $|n\rangle\langle n|$, and the environmental partial trace. All density operators are positive trace class with trace one, and all Hilbert spaces are untruncated.
--
--   For a channel defined by its fixed unitary and pure number environment, let $\Phi^c$ denote the channel obtained by tracing the system instead of that environment. On every trace-class input,
--
--   $$A(\kappa;n)^c=C(\sqrt{\kappa^2-1};n)\quad(\kappa\ge1),\qquad B(\kappa;n)^c=B(\sqrt{1-\kappa^2};n)\quad(0\le\kappa\le1).$$
--
--   Both relations use the same dilation as the original channel and hold for every $n\ge0$, including the endpoints. They identify the channel pairs needed for the entropy comparison.
-- source:
--   Non-Gaussian operations on bosonic modes of light: Photon-added Gaussian channels, arXiv:1604.07859v4, PDF p. 9, Proposition 8

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P20

noncomputable section

open Filter MeasureTheory

open scoped BigOperators Topology ENNReal

namespace QAlgorithms.Papers.Independent.Advance50.P20

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsTraceClass IsTraceClassChannel rankOne productCoeff traceSize)

open QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator fockKet fockDyad HasFockMatrix operatorOfMatrix KrausComplete
    CoherentRealized IsClassical husimiQ)

open QAlgorithms.Papers.Independent.Frontier18.P18
  (operatorCoeff boundedOperator conjugateCoeff IsKrausRepresentation)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation unitaryCoeff conjugateKernel partialRight partialLeft dilationReceiver weakComplement
    boundedUnitaryConjugation traceClassTensorPower operationalTraceClassCapacity)

open QAlgorithms.Papers.Independent.Claimed50.P35
  (InterleavedPhase ScaledWeylRepresentation physicalCommutationMatrix
    weylTraceCharacteristic LinearBosonic)

-- Accepted extended bit entropy and mean-photon thermal coefficients.

open QAlgorithms.Papers.Independent.Gap48.P26 (entropyBits thermalKernel)

open QAlgorithms.Papers.Independent.Claimed50.P39 (thermalProbability)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 8, PDF p.9 and Appendix VI B, PDF p.19: complements from
THE SAME dilation and number environment, including identity and replacer
endpoints. The missing environment parity in printed (59) is a global sign
on |n> and cancels from the channel; no incorrect unitary identity is asserted. -/
theorem complementaryPhotonChannels :
    (∀ k : ℝ, 1 ≤ k → ∀ n : ℕ,
      DilationRealized .amplifier k ∧
      DilationRealized .conjugator (Real.sqrt (k ^ 2 - 1)) ∧
      ∀ X, IsTraceClass X →
        photonComplement .amplifier k n X =
          photonChannel .conjugator (Real.sqrt (k ^ 2 - 1)) n X) ∧
    (∀ k : ℝ, 0 ≤ k → k ≤ 1 → ∀ n : ℕ,
      DilationRealized .attenuator k ∧
      DilationRealized .attenuator (Real.sqrt (1 - k ^ 2)) ∧
      ∀ X, IsTraceClass X →
        photonComplement .attenuator k n X =
          photonChannel .attenuator (Real.sqrt (1 - k ^ 2)) n X) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P20

end
