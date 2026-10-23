-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_generalized_ensemble_capacity_and_deficit
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.generalized_ensemble_capacity_and_deficit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:50:00.421192+00:00
-- url     : https://prove2.me/theorems/3564dcfa-28da-457d-94f1-7aca4a6d182d
-- title:
--   §4.3: generalized-ensemble bounds and supremum
-- statement:
--   Let $A$ be nonempty, closed, and of finite capacity. If $\mathcal M(A)$ is the set of Borel probability laws concentrated on $A$, then
--
--   $$\bar C(A)=\sup_{\mu\in\mathcal M(A)}\chi(\mu).$$
--
--   For every such law, with average $\bar\rho$, one has $\int D(\rho\|\Omega(A))\,d\mu\le\bar C(A)$ and
--
--   $$\bar C(A)-\chi(\mu)\ge D(\bar\rho\|\Omega(A))\ge\tfrac12\|\bar\rho-\Omega(A)\|_1^2.$$
--
--   Both quantities subtracted in the deficit are finite; average entropy need not be finite. This extends the finite-ensemble bounds to arbitrary generalized ensembles.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 39, §4.3: generalized-ensemble bounds and supremum

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P18

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState traceSize traceClosure IsTraceClassChannel productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble HasFiniteSupport HasAverage averageCoefficients
   extendedEntropyNats extendedRelativeEntropyNats
   finiteEnsembleCapacity pureStates)

open QAlgorithms.Papers.Independent.Frontier18.P01 (traceFirst traceSecond)

namespace QAlgorithms.Papers.Independent.Gap48.P18

attribute [local instance] Classical.propDecidable Classical.decEq

/-- §4.3: generalized-ensemble bounds and supremum, arXiv:quant-ph/0510073v2, PDF pp.39.
 -/
theorem generalized_ensemble_capacity_and_deficit {I : Type} [Countable I] [Nonempty I]
    (A : Set (State I)) (hA : A.Nonempty) (hclosed : IsClosed A)
    (hfinite : setChiCapacity A < ⊤) :
    setChiCapacity A = (⨆ mu : {mu : GeneralizedEnsemble I //
      MeasureConcentratedOn (mu : Measure (State I)) A}, measureHolevo (mu.val : Measure (State I))) ∧
    ∀ mu : GeneralizedEnsemble I, MeasureConcentratedOn (mu : Measure (State I)) A →
      (∫⁻ rho, stateRelativeEntropyNats rho (optimalAverage A hA) ∂(mu : Measure (State I))) ≤ setChiCapacity A ∧
      measureHolevo (mu : Measure (State I)) < ⊤ ∧
      stateRelativeEntropyNats (probabilityAverage mu) (optimalAverage A hA) < ⊤ ∧
      stateRelativeEntropyNats (probabilityAverage mu) (optimalAverage A hA) ≤
        ENNReal.ofReal ((setChiCapacity A).toReal - (measureHolevo (mu : Measure (State I))).toReal) ∧
      distanceSquared (probabilityAverage mu) (optimalAverage A hA) / 2 ≤
        stateRelativeEntropyNats (probabilityAverage mu) (optimalAverage A hA) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
