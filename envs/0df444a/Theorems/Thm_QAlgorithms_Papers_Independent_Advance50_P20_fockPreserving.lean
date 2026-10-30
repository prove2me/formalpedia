-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P20_fockPreserving
-- name    : QAlgorithms.Papers.Independent.Advance50.P20.fockPreserving
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:32:07.309085+00:00
-- url     : https://prove2.me/theorems/a1d7df3d-a22b-4028-95fc-2807c503fdfb
-- title:
--   Photon-added channels preserve Fock-diagonal states
-- statement:
--   Let $\mathcal H=\ell^2(\mathbb N)$, with normalized number states $|j\rangle$, and let $n\in\mathbb N$ be the environment photon number. Write $A(\kappa;n)$, $B(\kappa;n)$ and $C(\kappa;n)$ for the canonical amplifier, attenuator and phase-conjugator channels, respectively. Their amplitude domains are $\kappa\ge1$, $0\le\kappa\le1$ and $\kappa\ge0$. Each channel is defined by its specified two-mode unitary, the product environment $|n\rangle\langle n|$, and the environmental partial trace. All density operators are positive trace class with trace one, and all Hilbert spaces are untruncated.
--
--   Let $\mathcal D$ be the cone of positive trace-class operators diagonal in the number basis. Then for all three canonical families,
--
--   $$\Phi(\mathcal D)\subseteq\mathcal D.$$
--
--   In particular every normalized Fock-diagonal density has a normalized Fock-diagonal output. The cone version permits arbitrary finite trace and does not require trace one. This is the paper's coherence non-generation property in the Fock basis.
-- source:
--   Non-Gaussian operations on bosonic modes of light: Photon-added Gaussian channels, arXiv:1604.07859v4, PDF p. 12, Proposition 11

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

/-- Proposition 11, PDF pp.11--12, Eq.(36): normalized diagonal inputs remain
diagonal. Also retain the source's unnormalized positive trace-class cone D;
positivity and trace class are required, but trace one is not required there. -/
theorem fockPreserving (c : PhotonFamily) (k : ℝ) (hk : PhotonParameter c k) (n : ℕ) :
    DilationRealized c k ∧ IsTraceClassChannel (photonChannel c k n) ∧
    (∀ rho : State ℕ, FockDiagonal rho.coefficients →
      IsDensity (photonChannel c k n rho.coefficients) ∧
      FockDiagonal (photonChannel c k n rho.coefficients)) ∧
    (∀ X : Matrix ℕ ℕ ℂ, IsTraceClass X → FockDiagonal X →
      (∀ i, (X i i).im = 0 ∧ 0 ≤ (X i i).re) →
      IsTraceClass (photonChannel c k n X) ∧ FockDiagonal (photonChannel c k n X) ∧
      ∀ i, (photonChannel c k n X i i).im = 0 ∧
        0 ≤ (photonChannel c k n X i i).re) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P20

end
