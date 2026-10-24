-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P34_corollary8_contractionSums
-- name    : QAlgorithms.Papers.Independent.Support50.P34.corollary8_contractionSums
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:50:46.314961+00:00
-- url     : https://prove2.me/theorems/b070f783-fa1f-4fa1-b03f-eea73249d779
-- title:
--   Corollary 8: contractions and finite sums
-- statement:
--   Let $n,m\ge1$ and let $A_1,\ldots,A_n$ be subsets of the positive trace-class cone with the uniform approximation property. For independently chosen contractions $V_{ij}\in B(\mathcal H)$, the homogeneous quantum entropy is finite continuous on
--
--   $$\operatorname{cl}\!\left\{\sum_{i=1}^n\sum_{j=1}^m V_{ij}X_iV_{ij}^*:X_i\in A_i,\ \|V_{ij}\|\le1\right\}.$$
--
--   The same $X_i$ occurs in each of its $j$ summands, and the closure is in trace norm. This result requires no channel completeness relation among the contractions.
-- source:
--   Continuity of the von Neumann entropy, arXiv:0904.1963v3, PDF p. 32, Corollary 8: contractions and finite sums

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

/-- Corollary 8, arXiv:0904.1963v3, PDF p.32: finite sums of arbitrary independent
contractions, followed by trace-norm closure. No Kraus completeness is required. -/
theorem corollary8_contractionSums (b : HilbertBasis I ℂ H) (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) (A : Fin n → Set (PositiveCone H))
    (hA : ∀ i, HasUA b (A i)) :
    FiniteEntropyContinuousOn (coneEntropy b) (closure (contractionSumSet (m := m) A)) := by sorry

end Statements

end Operators

end QAlgorithms.Papers.Independent.Support50.P34

end
