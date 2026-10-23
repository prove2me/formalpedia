-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P18_entropy_maximizing_sequences_common_limit
-- name    : QAlgorithms.Papers.Independent.Gap48.P18.entropy_maximizing_sequences_common_limit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:35:41.903967+00:00
-- url     : https://prove2.me/theorems/4babdbbe-353c-4e93-85b6-15deeec8ed85
-- title:
--   Lemma 2
-- statement:
--   Let $A$ be a nonempty closed convex set of density states, with finite entropy supremum $S=\sup_{\rho\in A}H(\rho)$. There is a unique state $\rho_*(A)\in A$ such that every sequence $\rho_n\in A$ satisfying $H(\rho_n)\to S$ obeys
--
--   $$\rho_n\longrightarrow\rho_*(A)\quad\text{in trace norm}.$$
--
--   If an entropy maximizer $\Gamma(A)$ exists, it equals $\rho_*(A)$ and entropy restricted to $A$ is finite and continuous at $\Gamma(A)$. The common limit need not itself attain the supremum.
-- source:
--   Entropic characteristics of subsets of states, arXiv:quant-ph/0510073v2, PDF p. 7, Lemma 2

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

/-- Lemma 2, arXiv:quant-ph/0510073v2, PDF pp.7.
 -/
theorem entropy_maximizing_sequences_common_limit {I : Type} [Countable I] [Nonempty I]
    (A : Set (State I)) (hA : A.Nonempty) (hclosed : IsClosed A)
    (hconvex : CoefficientConvexStates A) (hfinite : entropySup A < ⊤) :
    ∃! omega : State I, omega ∈ A ∧
      (∀ seq : ℕ → State I, (∀ n, seq n ∈ A) →
        Tendsto (fun n => stateEntropyNats (seq n)) atTop (𝓝 (entropySup A)) →
          Tendsto seq atTop (𝓝 omega)) ∧
      (∀ gamma ∈ A, stateEntropyNats gamma = entropySup A →
        gamma = omega ∧ FiniteContinuousWithinAt stateEntropyNats A gamma) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P18

end
