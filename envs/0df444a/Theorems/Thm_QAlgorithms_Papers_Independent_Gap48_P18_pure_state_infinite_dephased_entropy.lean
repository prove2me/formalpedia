-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_pure_state_infinite_dephased_entropy
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.pure_state_infinite_dephased_entropy
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:47:42.488926+00:00
-- url     : https://prove2.me/theorems/e022203c-8f55-450f-81bd-19e3c5d3b9c3
-- title:
--   Remark 4
-- statement:
--   In an infinite-dimensional separable Hilbert space, one can choose a pure state $\rho$ and an orthonormal basis $b$ whose classical projection has
--
--   $$H(\Pi_b(\rho))=\infty.$$
--
--   In coordinates the chosen basis is the coordinate basis. This witnesses why the existential basis clauses in Proposition 5 cannot be made universal.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 22, Remark 4

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

/-- Remark 4, arXiv:quant-ph/0510073v2, PDF pp.22.
 -/
theorem pure_state_infinite_dephased_entropy {I : Type} [Countable I] [Infinite I] :
    ∃ rho : PureState I, extendedEntropyNats (Matrix.diagonal (Matrix.diag rho.val.coefficients)) = ⊤ := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
