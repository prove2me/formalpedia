-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P34_remark7_normalization
-- name    : QAlgorithms.Papers.Independent.Support50.P34.remark7_normalization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:51:24.561602+00:00
-- url     : https://prove2.me/theorems/e0020106-2442-466e-b8b3-8fb568c8d08e
-- title:
--   Remark 7: continuity after normalization
-- statement:
--   Let $A$ be a subset of the positive trace-class cone on which homogeneous quantum entropy is finite continuous. Suppose there exists a uniform constant $c>0$ such that $\operatorname{Tr}T\ge c$ for every $T\in A$. Then von Neumann entropy is finite continuous on the normalized state set
--
--   $$\left\{\frac{T}{\operatorname{Tr}T}:T\in A\right\}\subseteq S(\mathcal H).$$
--
--   Normalization is computed from each operator's trace. This transports the cone continuity conditions to states using the source's uniform positive trace bound.
-- source:
--   Continuity of the von Neumann entropy, arXiv:0904.1963v3, PDF p. 34, Remark 7: continuity after normalization

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

/-- Remark 7, arXiv:0904.1963v3, PDF p.34: the trace lower bound is uniform. -/
theorem remark7_normalization (b : HilbertBasis I ℂ H) (A : Set (PositiveCone H))
    (hentropy : FiniteEntropyContinuousOn (coneEntropy b) A)
    (htrace : ∃ c : ℝ, 0 < c ∧ ∀ T ∈ A, c ≤ (operatorTrace b (coneOp T)).re) :
    FiniteEntropyContinuousOn (fun rho : QuantumState b => stateEntropy b rho)
      (normalizedConeSet b A) := by sorry

end Statements

end Operators

end QAlgorithms.Papers.Independent.Support50.P34

end
