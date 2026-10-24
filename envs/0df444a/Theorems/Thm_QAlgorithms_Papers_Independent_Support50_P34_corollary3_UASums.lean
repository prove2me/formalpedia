-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P34_corollary3_UASums
-- name    : QAlgorithms.Papers.Independent.Support50.P34.corollary3_UASums
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:48:00.290745+00:00
-- url     : https://prove2.me/theorems/e8407f28-7dbd-47a8-a09f-cb3a08a99030
-- title:
--   Corollary 3 (A–B): sums and convex unions preserve UA
-- statement:
--   Let $A,B$ be subsets of the positive trace-class cone with the uniform approximation property, meaning $\sup_{T\in A}\Delta_k(T)\to0$ and the analogous condition for $B$, where $\Delta_k$ is the rank-constrained relative-entropy defect. Then
--
--   $$A\boxplus B=\{X+Y:X\in A,\ Y\in B\}$$
--
--   has the same property. If $A$ and $B$ are convex, their trace-norm closed convex hull $\overline{\operatorname{co}}(A\cup B)$ also has the property. This gives both closure operations without imposing compactness.
-- source:
--   Continuity of the von Neumann entropy, arXiv:0904.1963v3, PDF p. 27, Corollary 3 (A–B): sums and convex unions preserve UA

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

/-- Corollary 3 A–B, arXiv:0904.1963v3, PDF p.27: sums and closed convex unions. -/
theorem corollary3_UASums (b : HilbertBasis I ℂ H)
    (A B : Set (PositiveCone H)) (hA : HasUA b A) (hB : HasUA b B) :
    HasUA b (coneSumSet A B) ∧
    (ConeConvex A → ConeConvex B → HasUA b (coneClosedHull (A ∪ B))) := by sorry

end Statements

end Operators

end QAlgorithms.Papers.Independent.Support50.P34

end
