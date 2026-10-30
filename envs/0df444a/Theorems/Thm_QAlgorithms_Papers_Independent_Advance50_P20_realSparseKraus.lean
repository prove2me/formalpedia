-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P20_realSparseKraus
-- name    : QAlgorithms.Papers.Independent.Advance50.P20.realSparseKraus
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:35:01.640395+00:00
-- url     : https://prove2.me/theorems/15a35820-a78a-4dc9-900e-ace3b5f86b3c
-- title:
--   Real sparse Kraus families and the conjugator rank bound
-- statement:
--   Let $\mathcal H=\ell^2(\mathbb N)$, with normalized number states $|j\rangle$, and let $n\in\mathbb N$ be the environment photon number. Write $A(\kappa;n)$, $B(\kappa;n)$ and $C(\kappa;n)$ for the canonical amplifier, attenuator and phase-conjugator channels, respectively. Their amplitude domains are $\kappa\ge1$, $0\le\kappa\le1$ and $\kappa\ge0$. Each channel is defined by its specified two-mode unitary, the product environment $|n\rangle\langle n|$, and the environmental partial trace. All density operators are positive trace class with trace one, and all Hilbert spaces are untruncated.
--
--   For the displayed bounded Kraus representations, all number-basis coefficients are real. Their only possible nonzero entries obey
--
--   $$\begin{array}{ll}A_\ell:&m+n=j+\ell,\\ B_\ell:&m+\ell=j+n,\\ C_\ell:&m+j=n+\ell.\end{array}$$
--
--   The first two families occupy shifted diagonals, while the conjugator occupies a finite anti-diagonal and satisfies
--
--   $$\operatorname{rank} C_\ell(\kappa;n)\le n+\ell+1.$$
--
--   This is an upper support and rank statement. Interference and endpoint zeros are permitted. It identifies a useful real representation without claiming that every permitted entry is nonzero.
-- source:
--   Non-Gaussian operations on bosonic modes of light: Photon-added Gaussian channels, arXiv:1604.07859v4, PDF p. 7, §III, unnumbered: real and sparse Kraus structure

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

/-- Section III, PDF pp.5--7: real shifted diagonals for A/B, real finite
anti-diagonals for C. Only a rank upper bound is claimed; allowed entries can
vanish by interference or at endpoints. -/
theorem realSparseKraus (c : PhotonFamily) (k : ℝ) (hk : PhotonParameter c k) (n : ℕ) :
    DilationRealized c k ∧ KrausRealized c k n ∧
    IsKrausRepresentation (photonChannel c k n) (photonKraus c k n) ∧
    ∀ ell,
      (∀ m j, (operatorCoeff (photonKraus c k n ell) m j).im = 0) ∧
      (∀ m j, krausEntry c k n ell m j ≠ 0 →
        match c with
        | .amplifier => m + n = j + ell
        | .attenuator => m + ell = j + n
        | .conjugator => m + j = n + ell) ∧
      (c = .conjugator → Module.rank ℂ
        (LinearMap.range (photonKraus c k n ell).toLinearMap) ≤
          (n + ell + 1 : Cardinal)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P20

end
