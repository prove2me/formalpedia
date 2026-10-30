-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P20_noisyPreparationsAgree
-- name    : QAlgorithms.Papers.Independent.Advance50.P20.noisyPreparationsAgree
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:37:26.501862+00:00
-- url     : https://prove2.me/theorems/2ca75868-67d8-46eb-b5d5-0643e31137b2
-- title:
--   Pure and mixed photon-added noisy preparations induce the same channels
-- statement:
--   Let $\mathcal H=\ell^2(\mathbb N)$, with normalized number states $|j\rangle$, and let $n\in\mathbb N$ be the environment photon number. Write $A(\kappa;n)$, $B(\kappa;n)$ and $C(\kappa;n)$ for the canonical amplifier, attenuator and phase-conjugator channels, respectively. Their amplitude domains are $\kappa\ge1$, $0\le\kappa\le1$ and $\kappa\ge0$. Each channel is defined by its specified two-mode unitary, the product environment $|n\rangle\langle n|$, and the environmental partial trace. All density operators are positive trace class with trace one, and all Hilbert spaces are untruncated.
--
--   For a finite thermal mean $\bar N\ge0$, define
--
--   $$q_j=\binom{j+n}{n}\frac{\bar N^j}{(1+\bar N)^{j+n+1}},\qquad |\Psi_{\bar N,n}\rangle=\sum_{j=0}^\infty\sqrt{q_j}|j+n,j\rangle,\qquad \sigma_{\bar N,n}=\sum_{j=0}^\infty q_j|j+n\rangle\langle j+n|.$$
--
--   The $q_j$ form a probability law, $|\Psi_{\bar N,n}\rangle$ is a unit vector, and $\sigma_{\bar N,n}$ is a density operator with
--
--   $$\operatorname{Tr}_2|\Psi_{\bar N,n}\rangle\langle\Psi_{\bar N,n}|=\sigma_{\bar N,n}.$$
--
--   Applying the fixed canonical coupling to the input and the first environment mode, with the second untouched, gives a CPTP channel equal on every trace-class input to the channel formed by first tracing the second environment and then coupling to $\sigma_{\bar N,n}$. This includes all four cases $n=0$ or $n>0$ and $\bar N=0$ or $\bar N>0$. Photon addition acts on the first mode as a normalized postselected preparation.
-- source:
--   Non-Gaussian operations on bosonic modes of light: Photon-added Gaussian channels, arXiv:1604.07859v4, PDF p. 14, §IV H, unnumbered: pure and mixed photon-added noisy constructions agree

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

/-- Section IV H, PDF pp.14--15, Figs.16--17: the two normalized preparations
have the SAME partial trace and induce the SAME channel on every trace-class
input. Photon addition acts on the first environmental mode. n=0 and N=0
are retained; preparation itself is postselected, not a deterministic channel. -/
theorem noisyPreparationsAgree (c : PhotonFamily) (k : ℝ) (hk : PhotonParameter c k)
    (N : ℝ) (hN : 0 ≤ N) (n : ℕ) :
    DilationRealized c k ∧
    (∀ j, 0 ≤ addedThermalWeight N n j) ∧ HasSum (addedThermalWeight N n) 1 ∧
    (∀ p, addedPurification N n p = addedPurificationCoefficient N n p) ∧
    ‖addedPurification N n‖ = 1 ∧
    IsDensity (rankOne (addedPurification N n)) ∧ IsDensity (addedThermalEnvironment N n) ∧
    partialRight (rankOne (addedPurification N n)) = addedThermalEnvironment N n ∧
    IsTraceClassChannel (pureAddedNoisyChannel c k N n) ∧
    IsTraceClassChannel (mixedAddedNoisyChannel c k N n) ∧
    ∀ X, IsTraceClass X →
      pureAddedNoisyChannel c k N n X = mixedAddedNoisyChannel c k N n X := by sorry

end QAlgorithms.Papers.Independent.Advance50.P20

end
