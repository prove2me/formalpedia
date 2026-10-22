-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P27_contravariant_measure_reprepare
-- name    : QAlgorithms.Papers.Independent.Gap48.P27.contravariant_measure_reprepare
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:19:30.381853+00:00
-- url     : https://prove2.me/theorems/bc9d5cb0-00c1-4ce8-8ea8-049cfdeeb0f3
-- title:
--   Proposition 5: exact coherent measure–reprepare representation
-- statement:
--   Let $\Phi$ be a quantum-limited Gaussian gauge-contravariant channel from $a$ input modes to $b$ output modes, with gain $K:\mathbb C^a\to\mathbb C^b$ and noise $(I+KK^*)/2$. For every input density $\rho\in\mathcal S_2$, write $|z\rangle=D(z)|0\rangle$ for the coherent states. Then
--
--   $$
--   \Phi[\rho]=\int_{\mathbb C^a}\frac{d^{2a}z}{\pi^a}
--   |-K\overline z\rangle\langle-K\overline z|\,\langle z|\rho|z\rangle.
--   $$
--
--   Every scalar coefficient integral is integrable. The integration dimension is the input mode count, and both the minus sign and the input conjugation are essential. This is an explicit representation derived for the channel, not an assumed preparation law.
-- source:
--   A solution of the Gaussian optimizer conjecture, arXiv:1312.2251v2, PDF p. 14, Proposition 5: exact coherent measure–reprepare representation

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

/-- Proposition 5, PDF p.14, (31): the exact heterodyne re-preparation
identity. Preserve BOTH the minus sign and conjugated input amplitude.
Integration is over the input phase space; scalar integrability is a conclusion. -/
theorem contravariant_measure_reprepare {a b : ℕ} (G : GaugeChannel a b)
    (hG : quantumLimitedContravariant G) (rho : State (NumberString a))
    (hrho : finiteSecondMoments rho.coefficients) :
    (∀ m n, Integrable (fun z : Fin a → ℂ =>
      (husimi rho.coefficients z : ℂ) *
        productCoherentKernel b (-(G.gain.mulVec (fun j => star (z j)))) m n)) ∧
    G.operation rho.coefficients = coherentMeasurePrepare
      (fun z => -(G.gain.mulVec (fun j => star (z j)))) rho.coefficients := by sorry

end QAlgorithms.Papers.Independent.Gap48.P27

end
