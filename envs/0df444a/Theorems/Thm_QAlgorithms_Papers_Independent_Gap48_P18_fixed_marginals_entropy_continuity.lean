-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_fixed_marginals_entropy_continuity
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.fixed_marginals_entropy_continuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:46:26.389132+00:00
-- url     : https://prove2.me/theorems/b2909614-5de9-4b31-880f-a4e3d7c9e6bd
-- title:
--   Corollary 12
-- statement:
--   For arbitrary density states $\rho$ and $\sigma$, let $C(\rho,\sigma)$ be all joint density states with these marginals. Then
--
--   $$H\big|_{C(\rho,\sigma)}\ \text{is finite and continuous}\iff H(\rho)<\infty\ \text{and}\ H(\sigma)<\infty.$$
--
--   The coupling set includes every entangled state with the prescribed marginals.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 62, Corollary 12

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

/-- Corollary 12, arXiv:quant-ph/0510073v2, PDF pp.62.
 -/
theorem fixed_marginals_entropy_continuity {I J : Type}
    [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (rho : State I) (sigma : State J) :
    FiniteContinuousOn stateEntropyNats (couplingSet rho sigma) ↔
      stateEntropyNats rho < ⊤ ∧ stateEntropyNats sigma < ⊤ := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
