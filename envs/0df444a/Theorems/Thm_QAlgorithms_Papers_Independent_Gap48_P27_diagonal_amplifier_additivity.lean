-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P27_diagonal_amplifier_additivity
-- name    : QAlgorithms.Papers.Independent.Gap48.P27.diagonal_amplifier_additivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:23:41.144954+00:00
-- url     : https://prove2.me/theorems/da4a734e-f560-4d96-964c-93089bd9ca95
-- title:
--   §3: additivity consequences for diagonal amplifiers
-- statement:
--   Let $\Phi$ be a diagonal quantum-limited multimode amplifier with nonnegative amplitude gains at least one, and let $\Psi$ be any Gaussian auxiliary channel. Let $\widehat S_\Phi$ denote the infimum of the mean output entropy over all Borel probability ensembles supported on $\mathcal S_2$ with a prescribed barycenter. For every normalized joint $\sigma_{AC}\in\mathcal S_2$ with marginals $\sigma_A,\sigma_C$,
--
--   $$
--   \widehat S_{\Phi\otimes\Psi}(\sigma_{AC})
--   \ge\widehat S_\Phi(\sigma_A)+\widehat S_\Psi(\sigma_C).
--   $$
--
--   Moreover the infimal output entropy of $\Phi\otimes\Psi$ equals the sum of the individual infimal output entropies, all with the same finite-moment domains. An optimizer for an arbitrary auxiliary channel is not asserted. These are precisely (20)-(21), transferred by complementarity.
-- source:
--   A solution of the Gaussian optimizer conjecture, arXiv:1312.2251v2, PDF p. 10, §3: additivity consequences for diagonal amplifiers

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P27

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal BigOperators Topology ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap48.P27

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsTraceClass IsTraceClassChannel rankOne
   productCoeff tensorApply traceSize BreaksTraceClassEntanglement)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats GeneralizedEnsemble HasAverage
   finiteEnsembleCapacity ensembleHolevo)

open QAlgorithms.Papers.Independent.Frontier18.P18
  (operatorCoeff boundedOperator conjugateCoeff)

open QAlgorithms.Papers.Independent.Next46.P32
  (NumberString FockKernel vacuum productCoherentKernel modeEnergy husimi FockPOVM
   realFockTracePair)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Claimed50.P35
  (traceClassTensorMap traceClassChannelPower)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation partialRight partialLeft isometryCoeff conjugateKernel)

/-- §3, PDF p.10: only (20)-(21) are asserted for diagonal limited amplifiers,
with Gaussian auxiliary channel in the adopted S2 domain. No assertion that
the amplifier itself is entanglement-breaking or has the arbitrary-channel
capacity additivity of an entanglement-breaking channel is inserted. -/
theorem diagonal_amplifier_additivity {s c d : ℕ} (gain : Fin s → ℝ)
    (hgain : ∀ j, 1 ≤ gain j) (A : GaugeChannel s s)
    (hA : quantumLimitedAmplifier A)
    (hKA : A.gain = Matrix.diagonal (fun j => (gain j : ℂ)))
    (B : DisplacedFockGaussianLaw c d) :
    outputEntropyAdditivity A.operation B.operation := by sorry

end QAlgorithms.Papers.Independent.Gap48.P27

end
