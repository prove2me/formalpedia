-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P34_theorem1_strongStability
-- name    : QAlgorithms.Papers.Independent.Support50.P34.theorem1_strongStability
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:38:16.56198+00:00
-- url     : https://prove2.me/theorems/8d33d76b-fe6d-40e0-8c27-c34e3bfe08c8
-- title:
--   Theorem 1: strong stability of quantum states
-- statement:
--   Let $\mathcal H$ be a separable complex Hilbert space and $k\ge1$ an integer. Let $S_k(\mathcal H)$ consist of density operators of rank at most $k$, and let $\mathcal P^a$ denote countably atomic Borel probability measures. Both barycenter maps
--
--   $$\mathcal P(S_k(\mathcal H))\longrightarrow S(\mathcal H),\qquad \mathcal P^a(S_k(\mathcal H))\longrightarrow S(\mathcal H)$$
--
--   are surjective and open. The domain topology is weak probability convergence, including its restriction to atomic measures; the target topology is trace norm. This is the strong stability property of quantum states.
-- source:
--   Continuity of the von Neumann entropy, arXiv:0904.1963v3, PDF p. 8, Theorem 1: strong stability of quantum states

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

/-- Theorem 1, arXiv:0904.1963v3, PDF p.8: strong stability, including both surjections. -/
theorem theorem1_strongStability (b : HilbertBasis I ℂ H) (k : ℕ) (hk : 0 < k) :
    (∀ rho : QuantumState b, ∃ mu : ProbabilityMeasure (rankStates b k),
      mu ∈ stateFiber b (rankStates b k) rho) ∧
    (∀ rho : QuantumState b, ∃ mu : ProbabilityMeasure (rankStates b k),
      AtomicProbability mu ∧ mu ∈ stateFiber b (rankStates b k) rho) ∧
    StateBarycenterOpen b (rankStates b k) ∧ AtomicBarycenterOpen b (rankStates b k) := by sorry

end Statements

end Operators

end QAlgorithms.Papers.Independent.Support50.P34

end
