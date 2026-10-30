-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P20_pairwiseMinimumOutputEntropy
-- name    : QAlgorithms.Papers.Independent.Advance50.P20.pairwiseMinimumOutputEntropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:31:21.26223+00:00
-- url     : https://prove2.me/theorems/9774b9ec-e087-4602-a081-aedd0e15ae98
-- title:
--   Attained equal minimum output entropies for complementary pairs
-- statement:
--   Let $\mathcal H=\ell^2(\mathbb N)$, with normalized number states $|j\rangle$, and let $n\in\mathbb N$ be the environment photon number. Write $A(\kappa;n)$, $B(\kappa;n)$ and $C(\kappa;n)$ for the canonical amplifier, attenuator and phase-conjugator channels, respectively. Their amplitude domains are $\kappa\ge1$, $0\le\kappa\le1$ and $\kappa\ge0$. Each channel is defined by its specified two-mode unitary, the product environment $|n\rangle\langle n|$, and the environmental partial trace. All density operators are positive trace class with trace one, and all Hilbert spaces are untruncated.
--
--   Write $S$ for extended von Neumann entropy in bits. For either pair $(\Phi,\Psi)=(A(\kappa;n),C(\sqrt{\kappa^2-1};n))$ or $(B(\kappa;n),B(\sqrt{1-\kappa^2};n))$, with the respective parameter domains above, there exist an extended nonnegative value $h$ and a normalized pure input $\rho_*$ such that
--
--   $$S(\Phi(\rho_*))=S(\Psi(\rho_*))=h,\qquad h\le S(\Phi(\rho)),\quad h\le S(\Psi(\rho))\quad\text{for every density }\rho.$$
--
--   Thus the two minimum output entropies agree and are attained. This retains the source's invocation of a pure optimal input, without specifying its form or an entropy value.
-- source:
--   Non-Gaussian operations on bosonic modes of light: Photon-added Gaussian channels, arXiv:1604.07859v4, PDF p. 9, Corollary 9

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

/-- Corollary 9, PDF pp.9--10: both pairwise minimum output entropies,
including the source's pure optimizer and attainment, on all normalized inputs.
The extended entropy avoids any infinity-minus-infinity arithmetic. -/
theorem pairwiseMinimumOutputEntropy :
    (∀ k : ℝ, 1 ≤ k → ∀ n : ℕ,
      DilationRealized .amplifier k ∧
      DilationRealized .conjugator (Real.sqrt (k ^ 2 - 1)) ∧
      CommonAttainedMinimum (photonChannel .amplifier k n)
        (photonChannel .conjugator (Real.sqrt (k ^ 2 - 1)) n)) ∧
    (∀ k : ℝ, 0 ≤ k → k ≤ 1 → ∀ n : ℕ,
      DilationRealized .attenuator k ∧
      DilationRealized .attenuator (Real.sqrt (1 - k ^ 2)) ∧
      CommonAttainedMinimum (photonChannel .attenuator k n)
        (photonChannel .attenuator (Real.sqrt (1 - k ^ 2)) n)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P20

end
