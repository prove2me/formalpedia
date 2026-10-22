-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P27_amplifier_attenuator_connection
-- name    : QAlgorithms.Papers.Independent.Gap48.P27.amplifier_attenuator_connection
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:25:13.256121+00:00
-- url     : https://prove2.me/theorems/6e31a43d-f1b1-48db-86f7-9651766fa352
-- title:
--   §6 Eq. (41): connected amplifier and attenuated-amplifier outputs
-- statement:
--   Fix amplitude gain $K>1$, the quantum-limited amplifier $\Phi$ of gain $K$, and its associated attenuator $\Phi_1$ of gain $\sqrt{K^2-1}/K$. For every normalized pure finite-moment input $\rho=|\psi\rangle\langle\psi|$, there exists a connecting partial isometry $V_\rho$ such that
--
--   $$
--   \Phi[\rho]=V_\rho(\Phi\circ\Phi_1)[\rho]V_\rho^*.
--   $$
--
--   The reverse conjugation also recovers $(\Phi\circ\Phi_1)[\rho]$, so the connection is isometric on its relevant support. The witness may depend on the pure input. This is the structural identity (41), rather than just equality of infimal output entropies.
-- source:
--   A solution of the Gaussian optimizer conjecture, arXiv:1312.2251v2, PDF p. 16, §6 Eq. (41): connected amplifier and attenuated-amplifier outputs

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

/-- §6, PDF pp.16-17, (39)-(41): pure-input dependent connecting partial
isometry, with amplitude gain K and attenuation sqrt(K^2-1)/K. -/
theorem amplifier_attenuator_connection (K : ℝ) (hK : 1 < K)
    (A L : GaugeChannel 1 1) (hA : quantumLimitedAmplifier A)
    (hL : quantumLimitedAttenuator L)
    (hKA : A.gain = Matrix.diagonal (fun _ => (K : ℂ)))
    (hKL : L.gain = Matrix.diagonal (fun _ => (Real.sqrt (K ^ 2 - 1) / K : ℂ)))
    (rho : PureState (NumberString 1)) (hrho : finiteSecondMoments rho.val.coefficients) :
    ∃ V : Hilbert (NumberString 1) →L[ℂ] Hilbert (NumberString 1),
      connectingPartialIsometry V (A.operation (L.operation rho.val.coefficients))
        (A.operation rho.val.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P27

end
