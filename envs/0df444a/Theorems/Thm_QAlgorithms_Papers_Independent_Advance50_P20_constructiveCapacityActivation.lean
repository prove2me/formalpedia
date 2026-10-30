-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P20_constructiveCapacityActivation
-- name    : QAlgorithms.Papers.Independent.Advance50.P20.constructiveCapacityActivation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:36:19.167831+00:00
-- url     : https://prove2.me/theorems/8b44ffcf-02be-4db8-8de6-7371397d07d4
-- title:
--   Constructive activation of quantum and private capacities
-- statement:
--   Let $\mathcal H=\ell^2(\mathbb N)$, with normalized number states $|j\rangle$, and let $n\in\mathbb N$ be the environment photon number. Write $A(\kappa;n)$, $B(\kappa;n)$ and $C(\kappa;n)$ for the canonical amplifier, attenuator and phase-conjugator channels, respectively. Their amplitude domains are $\kappa\ge1$, $0\le\kappa\le1$ and $\kappa\ge0$. Each channel is defined by its specified two-mode unitary, the product environment $|n\rangle\langle n|$, and the environmental partial trace. All density operators are positive trace class with trace one, and all Hilbert spaces are untruncated.
--
--   Use $\kappa_0=\sqrt{(3/2)^2-1}$ and the fixed normalized input $\rho_0=\tfrac35|0\rangle\langle0|+\tfrac25|1\rangle\langle1|$. Let $Q$ and $P$ denote unassisted memoryless quantum and private classical capacities in qubits/use and secret bits/use, without an input energy constraint. Write $S$ for entropy in bits. For every integer $1\le n\le10$, both output entropies below are finite and
--
--   $$S(C(\kappa_0;n)(\rho_0))-S(A(3/2;n)(\rho_0))>0,\qquad Q(C(\kappa_0;n))>0,\qquad P(C(\kappa_0;n))>0.$$
--
--   In contrast, $Q(C(\kappa_0;0))=P(C(\kappa_0;0))=0$. The amplifier in the difference is the complementary channel. This records the precise constructive activation claim for the fixed first-example state.
--
--   **Formalization Note** The source supplies numerical evidence with output cutoff 110, without certified tail bounds. The statement-with-sorry targets the exact infinite-dimensional strict inequality; printed decimal entropies are not asserted as exact identities. The amplitude uses the explicit first example and Fig.12, correcting the missing square in Table III's caption.
-- source:
--   Non-Gaussian operations on bosonic modes of light: Photon-added Gaussian channels, arXiv:1604.07859v4, PDF p. 11, §IV D.1, unnumbered: constructive quantum/private capacity activation

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

/-- Section IV D.1, PDF pp.10--12, Fig.12: exact strict positivity targeted by
truncated numerical evidence, not an exact claim for printed decimals. The
source uses cutoff 110 without certified tails; no completed proof is claimed.
The caption's missing square is corrected using the first example and gain 3/2.
Both entropies are finite before their real difference is taken. -/
theorem constructiveCapacityActivation :
    IsDensity activationInput ∧
    DilationRealized .conjugator activationAmplitude ∧
    DilationRealized .amplifier (3 / 2) ∧
    operationalTraceClassCapacity (photonChannel .conjugator activationAmplitude 0) = 0 ∧
    fullFockPrivateCapacity (photonChannel .conjugator activationAmplitude 0)
      (photonComplement .conjugator activationAmplitude 0) = 0 ∧
    ∀ n : ℕ, 1 ≤ n → n ≤ 10 →
      IsDensity (photonChannel .conjugator activationAmplitude n activationInput) ∧
      IsDensity (photonChannel .amplifier (3 / 2) n activationInput) ∧
      entropyBits (photonChannel .conjugator activationAmplitude n activationInput) ≠ ⊤ ∧
      entropyBits (photonChannel .amplifier (3 / 2) n activationInput) ≠ ⊤ ∧
      0 < (entropyBits (photonChannel .conjugator activationAmplitude n activationInput)).toReal -
        (entropyBits (photonChannel .amplifier (3 / 2) n activationInput)).toReal ∧
      0 < operationalTraceClassCapacity (photonChannel .conjugator activationAmplitude n) ∧
      0 < fullFockPrivateCapacity (photonChannel .conjugator activationAmplitude n)
        (photonComplement .conjugator activationAmplitude n) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P20

end
