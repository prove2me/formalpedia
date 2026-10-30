-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P20_environmentAssistedClassicalRecovery
-- name    : QAlgorithms.Papers.Independent.Advance50.P20.environmentAssistedClassicalRecovery
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:33:56.696209+00:00
-- url     : https://prove2.me/theorems/a467ce90-97a5-48d2-9d77-fa56549b453c
-- title:
--   Environment-assisted recovery of every Fock-basis message
-- statement:
--   Let $\mathcal H=\ell^2(\mathbb N)$, with normalized number states $|j\rangle$, and let $n\in\mathbb N$ be the environment photon number. Write $A(\kappa;n)$, $B(\kappa;n)$ and $C(\kappa;n)$ for the canonical amplifier, attenuator and phase-conjugator channels, respectively. Their amplitude domains are $\kappa\ge1$, $0\le\kappa\le1$ and $\kappa\ge0$. Each channel is defined by its specified two-mode unitary, the product environment $|n\rangle\langle n|$, and the environmental partial trace. All density operators are positive trace class with trace one, and all Hilbert spaces are untruncated.
--
--   Measure the environment in the number basis and make its outcome $y$ available to the receiver. For the specified Kraus operators $F_y$, there is one family of CPTP recovery maps $\{\mathcal R_y\}_{y\ge0}$, chosen independently of the message $j$, such that
--
--   $$\sum_{y=0}^\infty \mathcal R_y\!\left(F_y|j\rangle\langle j|F_y^\dagger\right)=|j\rangle\langle j|\qquad\text{for every }j\in\mathbb N.$$
--
--   The series converges in trace norm. This restores classical information encoded in Fock states, for all $n\ge0$ and all admissible amplitudes. Zero-probability branches are allowed and require no normalized conditional vector.
-- source:
--   Non-Gaussian operations on bosonic modes of light: Photon-added Gaussian channels, arXiv:1604.07859v4, PDF p. 13, Theorem 14

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

/-- Theorem 14, PDF pp.12--13, Eqs.(38)--(42): the environment's Fock outcome
y is available to the receiver. One family of CPTP recoveries is chosen before
all messages j, and the corrected branch sum converges in trace norm to |j><j|.
Zero-probability branches require no division and no normalized conditional ket. -/
theorem environmentAssistedClassicalRecovery (c : PhotonFamily) (k : ℝ)
    (hk : PhotonParameter c k) (n : ℕ) :
    DilationRealized c k ∧ KrausRealized c k n ∧
    IsKrausRepresentation (photonChannel c k n) (photonKraus c k n) ∧
    ∃ R : ℕ → Operation ℕ ℕ,
      (∀ y, IsTraceClassChannel (R y)) ∧
      ∀ j : ℕ, TraceSeries
        (fun y => R y (conjugateCoeff (photonKraus c k n y) (numberDensity j)))
        (numberDensity j) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P20

end
