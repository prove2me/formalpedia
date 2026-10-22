-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P27_single_mode_amplifier_minimum
-- name    : QAlgorithms.Papers.Independent.Gap48.P27.single_mode_amplifier_minimum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:25:45.537991+00:00
-- url     : https://prove2.me/theorems/2caf74ae-eeae-4fdd-9216-a093d9e75892
-- title:
--   §6: proof of hypothesis (A)
-- statement:
--   Let $\Phi$ be any one-mode quantum-limited amplifier, including identity gain. Among all normalized positive trace-class inputs $\rho$ with finite mean photon occupation, the vacuum $|0\rangle\langle0|$ attains the minimum:
--
--   $$
--   S(\Phi[\rho])\ge S(\Phi[|0\rangle\langle0|]).
--   $$
--
--   There is no uniform energy cap on the competitors. This establishes hypothesis (A); the pure-state inequality proved at the end of §6 extends to mixed inputs by entropy concavity, as required by (A). The auxiliary Gibbs parameter is internal to the proof.
-- source:
--   A solution of the Gaussian optimizer conjecture, arXiv:1312.2251v2, PDF p. 19, §6: proof of hypothesis (A)

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

/-- §6, PDF pp.15,19: proof of (A), including identity gain K=1. The
internal Gibbs parameter requires 0<gamma<1, although p.19 prints only
gamma>0; it is not a hypothesis on the final optimizer theorem. -/
theorem single_mode_amplifier_minimum : singleModeAmplifierHypothesis := by sorry

end QAlgorithms.Papers.Independent.Gap48.P27

end
