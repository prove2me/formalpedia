-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P27_finite_moments_closure
-- name    : QAlgorithms.Papers.Independent.Gap48.P27.finite_moments_closure
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:22:58.635981+00:00
-- url     : https://prove2.me/theorems/e35c2fba-30e0-4ab3-a71e-2b82daef4c31
-- title:
--   §3: finite-second-moment domain and finite entropy
-- statement:
--   Let $\Phi$ be any finite-mode Gaussian CPTP channel, allowing arbitrary real-linear phase transformations, displacement and Gaussian noise. If $\rho$ is a normalized state in $\mathcal S_2$, then
--
--   $$
--   \Phi[\rho]\in\mathcal S_2,\qquad S(\rho)<\infty,\qquad S(\Phi[\rho])<\infty.
--   $$
--
--   Its output-entropy convex closure at $\rho$ is finite. For any Borel probability ensemble supported almost everywhere on $\mathcal S_2$ with barycenter $\rho$, both its mean output entropy and its channel Holevo quantity are finite. All entropies use natural logarithms. These domain guarantees license the finite entropy differences used in the paper; no claim of finite relative entropy between arbitrary pairs of finite-energy states is made.
-- source:
--   A solution of the Gaussian optimizer conjecture, arXiv:1312.2251v2, PDF p. 9, §3: finite-second-moment domain and finite entropy

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

/-- §3, PDF pp.9-10: S2 is preserved by EVERY Gaussian channel, with finite
input/output von Neumann entropy, convex closure, and ensemble Holevo
quantities. This does not assert finite relative entropy for arbitrary pairs. -/
theorem finite_moments_closure {a b : ℕ} (G : DisplacedFockGaussianLaw a b)
    (rho : State (NumberString a)) (hrho : finiteSecondMoments rho.coefficients) :
    extendedEntropyNats rho.coefficients < ⊤ ∧
    IsDensity (G.operation rho.coefficients) ∧
    finiteSecondMoments (G.operation rho.coefficients) ∧
    extendedEntropyNats (G.operation rho.coefficients) < ⊤ ∧
    finiteMomentConvexClosure G.operation finiteSecondMoments rho < ⊤ ∧
    ∀ mu : GeneralizedEnsemble (NumberString a), HasAverage mu rho →
      (∀ᵐ sigma ∂(mu : Measure (State (NumberString a))),
        finiteSecondMoments sigma.coefficients) →
      (∫⁻ sigma : State (NumberString a),
        extendedEntropyNats (G.operation sigma.coefficients)
        ∂(mu : Measure (State (NumberString a)))) < ⊤ ∧
      ensembleHolevo G.operation mu < ⊤ := by sorry

end QAlgorithms.Papers.Independent.Gap48.P27

end
