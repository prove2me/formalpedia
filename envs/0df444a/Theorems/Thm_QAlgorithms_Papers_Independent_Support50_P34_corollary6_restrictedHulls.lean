-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P34_corollary6_restrictedHulls
-- name    : QAlgorithms.Papers.Independent.Support50.P34.corollary6_restrictedHulls
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:49:27.110232+00:00
-- url     : https://prove2.me/theorems/cb5bfc8d-27c2-494c-b5cd-ab3e75e4e0dd
-- title:
--   Corollary 6 (A–B): entropy on restricted convex hulls
-- statement:
--   Let $A$ be a subset of positive trace-class operators, and use homogeneous entropy $H$.
--
--   1. If $A$ is trace-norm closed and bounded, and $H$ is finite continuous and bounded on $A$, then $H$ is finite continuous on every $m$-term convex-combination set $\operatorname{co}_m(A)$, $m\ge1$.
--   2. If $A$ is compact and $H$ is finite continuous on $A$, and $P$ is a family of countable probability weights with uniformly vanishing homogeneous entropy tails, then
--
--   $$H\in C\!\left(\operatorname{cl}(\operatorname{co}_P(A))\right),\qquad \lim_{m\to\infty}\sup_{\pi\in P}H(\{\pi_i\}_{i>m})=0.$$
--
--   Here $\operatorname{co}_P(A)$ uses actual countable trace-norm averages with weights in $P$. This retains the bounded hypotheses in the first clause and both separate conclusions.
-- source:
--   Continuity of the von Neumann entropy, arXiv:0904.1963v3, PDF p. 30, Corollary 6 (A–B): entropy on restricted convex hulls

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

/-- Corollary 6 A–B, arXiv:0904.1963v3, PDF p.30: the bounded setting
in A is retained despite the separate unbounded-cone error in Proposition 5. -/
theorem corollary6_restrictedHulls (b : HilbertBasis I ℂ H)
    (A : Set (PositiveCone H)) :
    ((IsClosed A ∧ ConeBounded b A ∧ FiniteEntropyContinuousOn (coneEntropy b) A ∧
      (∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ T ∈ A, coneEntropy b T ≤ c)) →
      ∀ m : ℕ, 0 < m →
        FiniteEntropyContinuousOn (coneEntropy b) (finiteConeHull m A)) ∧
    (IsCompact A → FiniteEntropyContinuousOn (coneEntropy b) A →
      ∀ P : Set (ℕ → ℝ), UniformWeightTails P →
        FiniteEntropyContinuousOn (coneEntropy b) (closure (restrictedConeHull b A P))) := by sorry

end Statements

end Operators

end QAlgorithms.Papers.Independent.Support50.P34

end
