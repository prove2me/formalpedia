-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P27_conditional_vacuum_reduction
-- name    : QAlgorithms.Papers.Independent.Gap48.P27.conditional_vacuum_reduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:18:39.582243+00:00
-- url     : https://prove2.me/theorems/46a5aa2a-bc3a-4609-9ff8-a90ee7f631d6
-- title:
--   Proposition 4: conditional reduction to one-mode amplifiers
-- statement:
--   Assume (A): for every one-mode quantum-limited amplifier, the vacuum minimizes output entropy over all normalized states with finite second moments. Then for every finite-mode Gaussian gauge-covariant or gauge-contravariant channel $\Phi$ and every positive integer $n$,
--
--   $$
--   \min_{\rho^{(n)}\in\mathcal S_2}S(\Phi^{\otimes n}[\rho^{(n)}])=nS(\Phi[\rho_{\rm vac}]).
--   $$
--
--   For any finite nonempty collection $\Phi_1,\ldots,\Phi_N$ of these channels, the joint minimum equals both $\sum_j\min_{\rho_j\in\mathcal S_2}S(\Phi_j[\rho_j])$ and $\sum_jS(\Phi_j[\rho_{j,\rm vac}])$. All minima are attained by the corresponding product vacuum, and competing joint inputs may be entangled. This is the conditional reduction; the unconditional result is a separate item.
-- source:
--   A solution of the Gaussian optimizer conjecture, arXiv:1312.2251v2, PDF p. 11, Proposition 4: conditional reduction to one-mode amplifiers

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

/-- Proposition 4, PDF pp.11-12, (26)-(27): retain precisely the one-mode
amplifier hypothesis (A) in this conditional reduction. The unconditional
specialization is stated separately above. -/
theorem conditional_vacuum_reduction (hA : singleModeAmplifierHypothesis) :
    vacuumOptimizerAndAdditivity := by sorry

end QAlgorithms.Papers.Independent.Gap48.P27

end
