-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P34_proposition6_projectionCompactness
-- name    : QAlgorithms.Papers.Independent.Support50.P34.proposition6_projectionCompactness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:52:21.760715+00:00
-- url     : https://prove2.me/theorems/d34b29d0-7430-492e-96ba-bf26dd62bd08
-- title:
--   Proposition 6: finite-projection compactness criterion
-- statement:
--   Let $A$ be a trace-norm closed subset of $T_1(\mathcal H)$, the positive operators of trace at most one. Then
--
--   $$A\text{ is compact}\quad\Longleftrightarrow\quad\forall\varepsilon>0\ \exists\text{ finite-rank orthogonal projection }P_\varepsilon:\ \forall T\in A,\ \operatorname{Tr}((I-P_\varepsilon)T)<\varepsilon.$$
--
--   Orthogonal projections are self-adjoint and idempotent. The trace upper bound is retained for every operator, and a rank-zero projection is permitted. This is the finite-projection compactness criterion on the bounded source domain.
-- source:
--   Continuity of the von Neumann entropy, arXiv:0904.1963v3, PDF p. 36, Proposition 6: finite-projection compactness criterion

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

/-- Proposition 6, arXiv:0904.1963v3, PDF p.36: the trace-at-most-one compactness
criterion. Finite rank permits rank zero for the empty set. -/
theorem proposition6_projectionCompactness (b : HilbertBasis I ℂ H)
    (A : Set (PositiveCone H)) (hclosed : IsClosed A)
    (htrace : ∀ T ∈ A, (operatorTrace b (coneOp T)).re ≤ 1) :
    IsCompact A ↔ ∀ eps : ℝ, 0 < eps → ∃ P : H →L[ℂ] H,
      P.adjoint = P ∧ P.comp P = P ∧ (∃ k : ℕ, RankLE k P) ∧
      ∀ T ∈ A, (operatorTrace b (((ContinuousLinearMap.id ℂ H) - P).comp (coneOp T))).re < eps := by sorry

end Statements

end Operators

end QAlgorithms.Papers.Independent.Support50.P34

end
