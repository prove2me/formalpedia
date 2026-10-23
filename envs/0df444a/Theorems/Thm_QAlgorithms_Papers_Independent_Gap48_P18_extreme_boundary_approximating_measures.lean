-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_extreme_boundary_approximating_measures
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.extreme_boundary_approximating_measures
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:44:11.050532+00:00
-- url     : https://prove2.me/theorems/76887013-559e-4d99-b6db-54187d46af9e
-- title:
--   Lemma 5
-- statement:
--   For a nonempty closed convex finite-capacity set $A$, there exist Borel probability laws $\mu_n$ and $\mu_*$ concentrated on $\overline{\mathrm{Ext}(A)}$ such that $\mu_n\Rightarrow\mu_*$ weakly and
--
--   $$\bar\rho(\mu_*)=\Omega(A),\qquad D(\bar\rho(\mu_n)\|\Omega(A))\to0,\qquad\chi(\mu_n)\to\bar C(A).$$
--
--   This supplies approximating laws on the closed extreme boundary. Without regularity, no optimality of the limiting law is asserted.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 40, Lemma 5

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

/-- Lemma 5, arXiv:quant-ph/0510073v2, PDF pp.40.
PDF overlines verified by rendering p.40. -/
theorem extreme_boundary_approximating_measures {I : Type} [Countable I] [Nonempty I]
    (A : Set (State I)) (hA : A.Nonempty) (hclosed : IsClosed A)
    (hconvex : CoefficientConvexStates A) (hfinite : setChiCapacity A < ⊤) :
    ∃ (seq : ℕ → GeneralizedEnsemble I) (mu : GeneralizedEnsemble I),
      (∀ n, MeasureConcentratedOn (seq n : Measure (State I)) (extremeClosure A)) ∧
      MeasureConcentratedOn (mu : Measure (State I)) (extremeClosure A) ∧
      Tendsto seq atTop (𝓝 mu) ∧ probabilityAverage mu = optimalAverage A hA ∧
      HConverges (fun n => probabilityAverage (seq n)) (optimalAverage A hA) ∧
      Tendsto (fun n => measureHolevo (seq n : Measure (State I))) atTop (𝓝 (setChiCapacity A)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
