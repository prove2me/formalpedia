-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_strong_projection_capacity_and_average_approximation
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.strong_projection_capacity_and_average_approximation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:59:51.056237+00:00
-- url     : https://prove2.me/theorems/72879474-af5c-4081-86b2-7fbb3944f867
-- title:
--   Theorem 4
-- statement:
--   Let $A$ be a nonempty state set and let orthogonal projections $P_n$ converge strongly to the identity. No finite-rank, nesting, or monotonicity assumption is imposed. If $\bar C(A)<\infty$, normalization is eventually valid uniformly on $A$, image capacities are eventually finite, and
--
--   $$\bar C(\Theta_{P_n}(A))\to\bar C(A),\qquad\Omega(\Theta_{P_n}(A))\to\Omega(A)\ \text{in trace norm}.$$
--
--   Conversely, if some strongly exhaustive projection sequence has all normalization maps defined on $A$ and uniformly bounded image capacities, then $\bar C(A)<\infty$. Arbitrary initial terms outside the positive-trace domain do not affect the first limits.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 73, Theorem 4

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

/-- Theorem 4, arXiv:quant-ph/0510073v2, PDF pp.73.
Early empty images are totalized only for writing the average sequence. Eventual positive uniform mass, nonempty images, and finite image capacities are conclusions. -/
theorem strong_projection_capacity_and_average_approximation {I : Type}
    [Countable I] [Nonempty I] (A : Set (State I)) (hA : A.Nonempty)
    (P : ℕ → BoundedOrthogonalProjection I)
    (hstrong : ∀ v : QAlgorithms.RealRegisters.Hilbert I,
      Tendsto (fun n => (P n).operator v) atTop (𝓝 v)) :
    (setChiCapacity A < ⊤ →
      (∀ᶠ n in atTop, 0 < projectionSuccessInfimum (P n) A) ∧
      (∀ᶠ n in atTop, (projectionImage (P n) A).Nonempty ∧
        setChiCapacity (projectionImage (P n) A) < ⊤) ∧
      Tendsto (fun n => setChiCapacity (projectionImage (P n) A)) atTop (𝓝 (setChiCapacity A)) ∧
      Tendsto (fun n => projectedAverage (P n) A hA) atTop (𝓝 (optimalAverage A hA))) ∧
      ((∀ n, ∀ rho ∈ A, 0 < projectionMass (P n) rho) →
        (⨆ n, setChiCapacity (projectionImage (P n) A)) < ⊤ → setChiCapacity A < ⊤) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
