-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P20_diagonalKrausEffects
-- name    : QAlgorithms.Papers.Independent.Advance50.P20.diagonalKrausEffects
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:33:25.036528+00:00
-- url     : https://prove2.me/theorems/1bbcd1f4-931f-4195-8765-b42aec86351a
-- title:
--   All displayed Kraus effects are positive and Fock diagonal
-- statement:
--   Let $\mathcal H=\ell^2(\mathbb N)$, with normalized number states $|j\rangle$, and let $n\in\mathbb N$ be the environment photon number. Write $A(\kappa;n)$, $B(\kappa;n)$ and $C(\kappa;n)$ for the canonical amplifier, attenuator and phase-conjugator channels, respectively. Their amplitude domains are $\kappa\ge1$, $0\le\kappa\le1$ and $\kappa\ge0$. Each channel is defined by its specified two-mode unitary, the product environment $|n\rangle\langle n|$, and the environmental partial trace. All density operators are positive trace class with trace one, and all Hilbert spaces are untruncated.
--
--   For the explicit Kraus operators $F_\ell$ of each family, every effect is positive and diagonal in the number basis:
--
--   $$E_\ell=F_\ell^\dagger F_\ell\ge0,\qquad \langle j|E_\ell|h\rangle=0\quad(j\ne h),\qquad\ell\in\mathbb N.$$
--
--   Positivity is bounded-operator positivity on the full Hilbert space. These effects determine orthogonality of conditional outputs from distinct Fock messages and support environment-assisted classical correction.
-- source:
--   Non-Gaussian operations on bosonic modes of light: Photon-added Gaussian channels, arXiv:1604.07859v4, PDF p. 13, Proposition 13

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

/-- Proposition 13, PDF p.13, Appendix VI A, PDF pp.18--19: every effect
F_ell^dagger F_ell is positive as an operator and diagonal in the Fock basis.
This makes no assertion of independence within a diagonal or of extremality. -/
theorem diagonalKrausEffects (c : PhotonFamily) (k : ℝ) (hk : PhotonParameter c k) (n : ℕ) :
    DilationRealized c k ∧ KrausRealized c k n ∧
    ∀ ell,
      let E := (ContinuousLinearMap.adjoint (photonKraus c k n ell)).comp
        (photonKraus c k n ell)
      ContinuousLinearMap.adjoint E = E ∧
      (∀ u : Fock, 0 ≤ (inner (𝕜 := ℂ) u (E u)).re) ∧
      FockDiagonal (operatorCoeff E) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P20

end
