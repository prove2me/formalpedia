-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P20_phaseNonclassicalityActivation
-- name    : QAlgorithms.Papers.Independent.Advance50.P20.phaseNonclassicalityActivation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:29:29.308228+00:00
-- url     : https://prove2.me/theorems/95758069-7afb-4a30-a475-7c32deb11841
-- title:
--   Vacuum witnesses nonclassicality activation under photon addition
-- statement:
--   Let $\mathcal H=\ell^2(\mathbb N)$, with normalized number states $|j\rangle$, and let $n\in\mathbb N$ be the environment photon number. Write $A(\kappa;n)$, $B(\kappa;n)$ and $C(\kappa;n)$ for the canonical amplifier, attenuator and phase-conjugator channels, respectively. Their amplitude domains are $\kappa\ge1$, $0\le\kappa\le1$ and $\kappa\ge0$. Each channel is defined by its specified two-mode unitary, the product environment $|n\rangle\langle n|$, and the environmental partial trace. All density operators are positive trace class with trace one, and all Hilbert spaces are untruncated.
--
--   A state is classical when it is a positive probability-measure mixture of coherent projectors; Dirac masses are permitted. A channel is nonclassicality breaking when it produces a classical output for every normalized input. Then, for every $\kappa\ge0$,
--
--   $$C(\kappa;n)\text{ is nonclassicality breaking}\quad\Longleftrightarrow\quad n=0.$$
--
--   For every $n>0$, the normalized vacuum input gives a nonclassical output $\rho_{\rm out}=C(\kappa;n)(|0\rangle\langle0|)$ satisfying
--
--   $$\langle\tau|\rho_{\rm out}|\tau\rangle=0\quad(0\le\tau<n),\qquad Q_{\rho_{\rm out}}(0)=0,$$
--
--   where $Q_\rho(\alpha)=\langle\alpha|\rho|\alpha\rangle$ is the Husimi function. This is an explicit activation witness, including the pure number-state replacer at $\kappa=0$.
-- source:
--   Non-Gaussian operations on bosonic modes of light: Photon-added Gaussian channels, arXiv:1604.07859v4, PDF p. 8, Proposition 6

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

/-- Proposition 6, PDF pp.8--9, Eqs.(28)--(29): exactly n=0 is
nonclassicality breaking. For n>0 the normalized vacuum is an activation
witness, with no output photons below n and with a Husimi zero at the origin.
The claim includes k=0, where the output is the number projector |n><n|. -/
theorem phaseNonclassicalityActivation (k : ℝ) (hk : 0 ≤ k) (n : ℕ) :
    DilationRealized .conjugator k ∧ KrausRealized .conjugator k n ∧
    IsTraceClassChannel (photonChannel .conjugator k n) ∧ CoherentRealized ∧
    (∀ rho : State ℕ,
      HasFockMatrix (operatorOfMatrix (photonChannel .conjugator k n rho.coefficients))
        (photonChannel .conjugator k n rho.coefficients)) ∧
    ((∀ rho : State ℕ,
      IsClassical (operatorOfMatrix (photonChannel .conjugator k n rho.coefficients))) ↔ n = 0) ∧
    (0 < n → IsDensity (numberDensity 0) ∧
      IsDensity (photonChannel .conjugator k n (numberDensity 0)) ∧
      ¬ IsClassical (operatorOfMatrix (photonChannel .conjugator k n (numberDensity 0))) ∧
      husimiQ (operatorOfMatrix (photonChannel .conjugator k n (numberDensity 0))) 0 = 0 ∧
      ∀ tau < n, photonChannel .conjugator k n (numberDensity 0) tau tau = 0) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P20

end
