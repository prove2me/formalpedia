-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P34_lemma5_atomicFiberDense
-- name    : QAlgorithms.Papers.Independent.Support50.P34.lemma5_atomicFiberDense
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:39:25.406317+00:00
-- url     : https://prove2.me/theorems/380540e4-8df0-487c-9327-34ee99f47af4
-- title:
--   Lemma 5: atomic measures dense within rank-constrained barycenter fibers
-- statement:
--   For a separable complex Hilbert space $\mathcal H$, a state $\rho$, and an integer $k\ge1$, let $\mathcal P_\rho(S_k(\mathcal H))$ be the Borel probability measures supported on rank-at-most-$k$ states with barycenter exactly $\rho$. Then
--
--   $$\overline{\mathcal P^a_\rho(S_k(\mathcal H))}=\mathcal P_\rho(S_k(\mathcal H)),$$
--
--   where the closure is taken in that fiber with its relative weak topology, and $\mathcal P^a$ means countably atomic. Thus atomic approximation preserves the barycenter exactly.
-- source:
--   Continuity of the von Neumann entropy, arXiv:0904.1963v3, PDF p. 9, Lemma 5: atomic measures dense within rank-constrained barycenter fibers

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P34

noncomputable section

open Filter MeasureTheory

open scoped ENNReal NNReal BigOperators

namespace QAlgorithms.Papers.Independent.Support50.P34

open QAlgorithms.Papers.Independent.Dependency50.P13
  (State PositiveTraceClass traceNormValue stateTraceNormTopology traceNormTopology
   operatorTrace IsPositive IsTraceClass stateEntropy relativeEntropy entropyWeight)

open QAlgorithms.Papers.Independent.Dependency50.P25 (extendedIntegral)

open QAlgorithms.Papers.Independent.Frontier18.P01 (binaryEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

section Operators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {I : Type*}

section Statements

variable [hsep : TopologicalSpace.SeparableSpace H] [hI : Countable I]

include hsep hI

/-- Lemma 5, arXiv:0904.1963v3, PDF p.9: density inside each exact barycenter fiber. -/
theorem lemma5_atomicFiberDense (b : HilbertBasis I ℂ H) (k : ℕ) (hk : 0 < k)
    (rho : QuantumState b) :
    Dense {mu : {mu : ProbabilityMeasure (rankStates b k) //
      mu ∈ stateFiber b (rankStates b k) rho} | AtomicProbability mu.val} := by sorry

end Statements

end Operators

end QAlgorithms.Papers.Independent.Support50.P34

end
