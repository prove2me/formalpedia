-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_marginal_set_entropy_boundedness_and_continuity
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.marginal_set_entropy_boundedness_and_continuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:45:49.868393+00:00
-- url     : https://prove2.me/theorems/c6f86fb0-e6c3-43ca-b6a9-a62ea8221ba8
-- title:
--   Proposition 10
-- statement:
--   Let $A$ and $B$ be nonempty sets of density states on arbitrary nonzero separable Hilbert spaces. Let $A\otimes B$ denote all joint states whose two marginals belong to $A$ and $B$, including entangled states. Then
--
--   $$\sup_{\omega\in A\otimes B}H(\omega)<\infty\iff\sup_AH<\infty\ \text{and}\ \sup_BH<\infty.$$
--
--   Entropy is finite and continuous on $A\otimes B$ exactly when it is finite and continuous on both marginal sets. The nonempty assumptions are necessary for the reverse implications.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 62, Proposition 10

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

/-- Proposition 10, arXiv:quant-ph/0510073v2, PDF pp.62.
 -/
theorem marginal_set_entropy_boundedness_and_continuity {I J : Type}
    [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (A : Set (State I)) (B : Set (State J)) (hA : A.Nonempty) (hB : B.Nonempty) :
    (entropySup (jointMarginalConstraintSet A B) < ⊤ ↔ entropySup A < ⊤ ∧ entropySup B < ⊤) ∧
      (FiniteContinuousOn stateEntropyNats (jointMarginalConstraintSet A B) ↔
        FiniteContinuousOn stateEntropyNats A ∧ FiniteContinuousOn stateEntropyNats B) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
