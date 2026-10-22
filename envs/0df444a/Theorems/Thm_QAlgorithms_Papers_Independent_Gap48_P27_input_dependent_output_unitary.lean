-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P27_input_dependent_output_unitary
-- name    : QAlgorithms.Papers.Independent.Gap48.P27.input_dependent_output_unitary
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:24:43.919786+00:00
-- url     : https://prove2.me/theorems/2b4c8f55-458d-4f45-9262-d012e3911f77
-- title:
--   §5: input-dependent output unitary equivalence
-- statement:
--   Let $\Phi$ be a quantum-limited Gaussian gauge-contravariant channel with gain $K$. Define $\Psi_+$ by heterodyne measurement and coherent re-preparation with amplitude $\overline Kz$, as in (32). For every normalized $\rho\in\mathcal S_2$, there exists a unitary $U_\rho$ on the common output Fock space such that
--
--   $$
--   \Phi[\rho]=U_\rho\Psi_+[\rho]U_\rho^*.
--   $$
--
--   The order is $\forall\rho\,\exists U_\rho$; no fixed conjugacy of the two channels is asserted. This explicit output equivalence is useful separately from the equality of entropy values.
-- source:
--   A solution of the Gaussian optimizer conjecture, arXiv:1312.2251v2, PDF p. 15, §5: input-dependent output unitary equivalence

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

/-- §5, PDF p.15: for EACH input there EXISTS a unitary. This is not one
fixed unitary conjugating the two channels on every input. -/
theorem input_dependent_output_unitary {a b : ℕ} (G : GaugeChannel a b)
    (hG : quantumLimitedContravariant G) (rho : State (NumberString a))
    (hrho : finiteSecondMoments rho.coefficients) :
    ∃ U : Hilbert (NumberString b) ≃ₗᵢ[ℂ] Hilbert (NumberString b),
      G.operation rho.coefficients = conjugateCoeff U.toLinearIsometry.toContinuousLinearMap
        (skewPlus G.gain rho.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P27

end
