-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P27_quantum_limited_factorization
-- name    : QAlgorithms.Papers.Independent.Gap48.P27.quantum_limited_factorization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:16:19.175169+00:00
-- url     : https://prove2.me/theorems/e14fb218-20ad-4931-8ff5-e3a4528b13d5
-- title:
--   Proposition 1: quantum-limited channel factorization
-- statement:
--   Let $\Phi$ be a finite-mode bosonic Gaussian gauge channel with gain $K$ and Hermitian noise $\mu$. In the covariant case impose both inequalities $\mu\ge\pm(I-KK^*)/2$; in the contravariant case impose $\mu\ge(I+KK^*)/2$. There exist a quantum-limited attenuator $\Phi_1$ and a diagonalizable channel $\Phi_2$ such that
--
--   $$
--   \Phi[X]=\Phi_2[\Phi_1[X]]\quad\text{for every trace-class operator }X.
--   $$
--
--   The second factor is a quantum-limited amplifier in the covariant case and a quantum-limited gauge-contravariant channel in the contravariant case. Its intermediate mode count can be taken to be the original output mode count. The factors are existential witnesses determined by the channel; no invertibility of $K$ is required. This factorization reduces general noise to the limited channel classes.
-- source:
--   A solution of the Gaussian optimizer conjecture, arXiv:1312.2251v2, PDF p. 7, Proposition 1: quantum-limited channel factorization

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

/-- Proposition 1, PDF pp.7-8: both channel factorizations on the entire
trace class. No invertibility of K is required, including in the contravariant
case, where the proof uses the inverse on the supported subspace. -/
theorem quantum_limited_factorization {a b : ℕ} (G : GaugeChannel a b) :
    ∃ (A : GaugeChannel a b) (B : GaugeChannel b b),
      quantumLimitedAttenuator A ∧ diagonalizableGaugeChannel B ∧
      (if G.contravariant then quantumLimitedContravariant B
       else quantumLimitedAmplifier B) ∧
      ∀ X, IsTraceClass X → G.operation X = B.operation (A.operation X) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P27

end
