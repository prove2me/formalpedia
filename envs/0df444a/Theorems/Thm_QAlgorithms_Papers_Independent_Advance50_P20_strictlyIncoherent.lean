-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P20_strictlyIncoherent
-- name    : QAlgorithms.Papers.Independent.Advance50.P20.strictlyIncoherent
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:32:54.782001+00:00
-- url     : https://prove2.me/theorems/32d37aba-9e85-4329-85a8-b2bc1171f98a
-- title:
--   The displayed Kraus representation is strictly incoherent
-- statement:
--   Let $\mathcal H=\ell^2(\mathbb N)$, with normalized number states $|j\rangle$, and let $n\in\mathbb N$ be the environment photon number. Write $A(\kappa;n)$, $B(\kappa;n)$ and $C(\kappa;n)$ for the canonical amplifier, attenuator and phase-conjugator channels, respectively. Their amplitude domains are $\kappa\ge1$, $0\le\kappa\le1$ and $\kappa\ge0$. Each channel is defined by its specified two-mode unitary, the product environment $|n\rangle\langle n|$, and the environmental partial trace. All density operators are positive trace class with trace one, and all Hilbert spaces are untruncated.
--
--   Let $F_\ell$ be the corresponding explicit Kraus operators in Eqs.(14),(18),(22), and let $\Delta$ remove all off-diagonal number-basis entries. This family is a Kraus representation of $\Phi$ and satisfies
--
--   $$\Delta(F_\ell X F_\ell^\dagger)=F_\ell\Delta(X)F_\ell^\dagger\qquad\text{for every }\ell\in\mathbb N\text{ and every trace-class }X.$$
--
--   Thus each family supplies a strictly incoherent channel representation in the Fock basis. The per-outcome identity is stronger than preservation of diagonal inputs by the sum alone.
-- source:
--   Non-Gaussian operations on bosonic modes of light: Photon-added Gaussian channels, arXiv:1604.07859v4, PDF p. 12, Remark 12

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

/-- Remark 12, PDF p.12, Eq.(37): the SPECIFIC displayed countable Kraus
representation is strictly incoherent, per outcome, on every trace-class input. -/
theorem strictlyIncoherent (c : PhotonFamily) (k : ℝ) (hk : PhotonParameter c k) (n : ℕ) :
    DilationRealized c k ∧ KrausRealized c k n ∧
    IsKrausRepresentation (photonChannel c k n) (photonKraus c k n) ∧
    ∀ ell X, IsTraceClass X →
      fockDephase (conjugateCoeff (photonKraus c k n ell) X) =
        conjugateCoeff (photonKraus c k n ell) (fockDephase X) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P20

end
