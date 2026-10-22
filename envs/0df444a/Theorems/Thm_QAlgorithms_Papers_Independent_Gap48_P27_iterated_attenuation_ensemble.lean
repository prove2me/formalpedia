-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P27_iterated_attenuation_ensemble
-- name    : QAlgorithms.Papers.Independent.Gap48.P27.iterated_attenuation_ensemble
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:21:19.509986+00:00
-- url     : https://prove2.me/theorems/4de52ae9-07b9-4b22-8da6-81da6fa905d7
-- title:
--   Proposition 7: iterated attenuation ensemble decomposition
-- statement:
--   Fix amplitude gain $K>1$. Let $\Phi$ be the one-mode quantum-limited amplifier of gain $K$ and $\Phi_1$ the quantum-limited attenuator of gain $\sqrt{K^2-1}/K$. For every normalized pure input $\rho\in\mathcal S_2$ and positive integer $n$, there are probabilities $p_i$, normalized pure component states $\rho_i\in\mathcal S_2$ for positive weights, and partial isometries $U_i$ isometric on the supports of $\Phi[\rho_i]$, such that
--
--   $$
--   \Phi_1^n[\rho]=\sum_i p_i\rho_i,\qquad
--   \Phi[\rho]=\sum_i p_iU_i\Phi[\rho_i]U_i^*.
--   $$
--
--   Both sums converge in trace norm; weights are nonnegative, summable, and sum to one. Finite ensembles may be padded with zero weights. All witnesses may depend on $K,\rho,n$. The common ensemble is the key structural decomposition used in §6.
-- source:
--   A solution of the Gaussian optimizer conjecture, arXiv:1312.2251v2, PDF p. 17, Proposition 7: iterated attenuation ensemble decomposition

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

/-- Proposition 7, PDF pp.17-18, (42)-(43): positive attenuation iteration
count, and one common ensemble in both trace-norm sums. Every connecting map
may depend on K, rho, n and the component. The proof's p_j p_{j|i} on p.18
is an index slip for p_i p_{j|i}; the statement uses the correct single weights. -/
theorem iterated_attenuation_ensemble (K : ℝ) (hK : 1 < K)
    (A L : GaugeChannel 1 1) (hA : quantumLimitedAmplifier A)
    (hL : quantumLimitedAttenuator L)
    (hKA : A.gain = Matrix.diagonal (fun _ => (K : ℂ)))
    (hKL : L.gain = Matrix.diagonal (fun _ => (Real.sqrt (K ^ 2 - 1) / K : ℂ)))
    (rho : PureState (NumberString 1)) (hrho : finiteSecondMoments rho.val.coefficients)
    (n : ℕ) (hn : 0 < n) :
    ∃ (E : CountablePureEnsemble 1)
      (U : ℕ → (Hilbert (NumberString 1) →L[ℂ] Hilbert (NumberString 1))),
      (∀ i, 0 < E.weight i → sourcePartialIsometry (U i)
        (A.operation (E.state i).val.coefficients)) ∧
      traceSeries (fun i => (E.weight i : ℂ) • (E.state i).val.coefficients)
        ((L.operation^[n]) rho.val.coefficients) ∧
      traceSeries (fun i => (E.weight i : ℂ) •
        conjugateCoeff (U i) (A.operation (E.state i).val.coefficients))
        (A.operation rho.val.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P27

end
