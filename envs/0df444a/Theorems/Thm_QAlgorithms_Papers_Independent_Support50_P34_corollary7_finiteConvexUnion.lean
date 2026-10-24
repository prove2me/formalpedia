-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P34_corollary7_finiteConvexUnion
-- name    : QAlgorithms.Papers.Independent.Support50.P34.corollary7_finiteConvexUnion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:50:10.587045+00:00
-- url     : https://prove2.me/theorems/699599cc-c35a-4c8e-a9be-e39b23ba4e01
-- title:
--   Corollary 7: entropy continuity on a finite convex union
-- statement:
--   Let $m\ge1$ and let $A_1,\ldots,A_m$ be convex trace-norm closed bounded subsets of the positive trace-class cone. If homogeneous quantum entropy $H$ is finite continuous on each $A_i$, then
--
--   $$H\in C\!\left(\overline{\operatorname{co}}\left(\bigcup_{i=1}^m A_i\right)\right).$$
--
--   No separate entropy boundedness assumption is imposed. This is the finite convex-union continuity statement with all source conditions on every constituent set.
-- source:
--   Continuity of the von Neumann entropy, arXiv:0904.1963v3, PDF p. 31, Corollary 7: entropy continuity on a finite convex union

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

/-- Corollary 7, arXiv:0904.1963v3, PDF p.31: the closed convex hull of a
finite union; no extra entropy boundedness assumption is inserted. -/
theorem corollary7_finiteConvexUnion (b : HilbertBasis I ℂ H) (m : ℕ) (hm : 0 < m)
    (A : Fin m → Set (PositiveCone H))
    (hconv : ∀ i, ConeConvex (A i)) (hclosed : ∀ i, IsClosed (A i))
    (hbounded : ∀ i, ConeBounded b (A i))
    (hentropy : ∀ i, FiniteEntropyContinuousOn (coneEntropy b) (A i)) :
    FiniteEntropyContinuousOn (coneEntropy b) (coneClosedHull (⋃ i, A i)) := by sorry

end Statements

end Operators

end QAlgorithms.Papers.Independent.Support50.P34

end
