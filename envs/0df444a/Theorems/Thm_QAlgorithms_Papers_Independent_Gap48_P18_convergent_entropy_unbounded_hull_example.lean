-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_convergent_entropy_unbounded_hull_example
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.convergent_entropy_unbounded_hull_example
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:48:54.665677+00:00
-- url     : https://prove2.me/theorems/638c5c9a-d69c-43ab-ba5e-b045352e76f5
-- title:
--   Remark 9
-- statement:
--   There exists a trace-norm convergent sequence $\rho_n\to\rho_*$ of states on an infinite-dimensional separable Hilbert space such that every $H(\rho_n)$ is finite and
--
--   $$H(\rho_n)\to H(\rho_*)<\infty,\qquad\sup_{\rho\in\overline{\operatorname{co}}\{\rho_n\}}H(\rho)=\infty.$$
--
--   Convergence of individual entropies does not provide a bound on the entropy of the closed convex hull.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 43, Remark 9

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

/-- Remark 9, arXiv:quant-ph/0510073v2, PDF pp.43.
 -/
theorem convergent_entropy_unbounded_hull_example {I : Type} [Countable I] [Infinite I] :
    ∃ (seq : ℕ → State I) (rho : State I), Tendsto seq atTop (𝓝 rho) ∧
      (∀ n, stateEntropyNats (seq n) < ⊤) ∧ stateEntropyNats rho < ⊤ ∧
      Tendsto (fun n => stateEntropyNats (seq n)) atTop (𝓝 (stateEntropyNats rho)) ∧
      entropySup (stateClosedConvexHull (Set.range seq)) = ⊤ := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
