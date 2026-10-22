-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P27_skew_output_spectra
-- name    : QAlgorithms.Papers.Independent.Gap48.P27.skew_output_spectra
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:20:23.973543+00:00
-- url     : https://prove2.me/theorems/4346e2ed-e5e9-432b-8712-c3bc669fd022
-- title:
--   Proposition 6: skew channels have identical output spectra
-- statement:
--   Let $\Phi$ and $K$ be as in Proposition 5, and define $\Psi_\pm$ by the same heterodyne measurement followed by preparation of $|\pm\overline K z\rangle$. For each normalized input $\rho\in\mathcal S_2$, all three outputs are density operators, there exist output unitaries $U_\rho,V_\rho$, and
--
--   $$
--   \Phi[\rho]=U_\rho\Psi_+[\rho]U_\rho^*
--   =V_\rho\Psi_-[\rho]V_\rho^*.
--   $$
--
--   Consequently their spectra agree with multiplicities and $S(\Phi[\rho])=S(\Psi_+[\rho])=S(\Psi_-[\rho])$. The unitaries may depend on the input. Defining the skew channels from (32)-(33) retains arbitrary rectangular $K$ and avoids the faulty dimensions of (34).
-- source:
--   A solution of the Gaussian optimizer conjecture, arXiv:1312.2251v2, PDF p. 15, Proposition 6: skew channels have identical output spectra

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

/-- Proposition 6, PDF p.15: spectra with multiplicities, expressed by
unitary conjugacy on the common output space, and hence equal entropies.
The skew maps are the explicit integrals (32)-(33), avoiding the dimensionally
faulty Heisenberg formula (34). The unitaries may depend on rho. -/
theorem skew_output_spectra {a b : ℕ} (G : GaugeChannel a b)
    (hG : quantumLimitedContravariant G) (rho : State (NumberString a))
    (hrho : finiteSecondMoments rho.coefficients) :
    IsDensity (skewPlus G.gain rho.coefficients) ∧
    IsDensity (skewMinus G.gain rho.coefficients) ∧
    (∃ U V : Hilbert (NumberString b) ≃ₗᵢ[ℂ] Hilbert (NumberString b),
      G.operation rho.coefficients = conjugateCoeff U.toLinearIsometry.toContinuousLinearMap
        (skewPlus G.gain rho.coefficients) ∧
      G.operation rho.coefficients = conjugateCoeff V.toLinearIsometry.toContinuousLinearMap
        (skewMinus G.gain rho.coefficients)) ∧
    extendedEntropyNats (skewPlus G.gain rho.coefficients) =
      extendedEntropyNats (G.operation rho.coefficients) ∧
    extendedEntropyNats (skewMinus G.gain rho.coefficients) =
      extendedEntropyNats (G.operation rho.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P27

end
