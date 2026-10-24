-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P34_reference33_choquetMaximality
-- name    : QAlgorithms.Papers.Independent.Support50.P34.reference33_choquetMaximality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:53:29.67879+00:00
-- url     : https://prove2.me/theorems/f2ca62df-8d40-44e7-8f14-ce82ca453e03
-- title:
--   Reference note [33]: maximality in the Choquet order
-- statement:
--   Let $\mu$ be a Borel probability measure supported on the pure states $S_1(\mathcal H)$, regarded as a probability on all states. Let $\nu$ be any Borel probability on $S(\mathcal H)$. If $\nu$ dominates $\mu$ in Choquet order, meaning
--
--   $$\int f\,d\nu\ge\int f\,d\mu\qquad\text{for every bounded continuous real convex }f,$$
--
--   then $\nu=\mu$. All state topology is trace norm. Thus pure-state-supported probabilities are maximal; the dominating measure need not already have pure-state support.
-- source:
--   Continuity of the von Neumann entropy, arXiv:0904.1963v3, PDF p. 42, Reference note [33]: maximality in the Choquet order

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

/-- Reference [33], arXiv:0904.1963v3, PDF p.42: pure-state-supported
probabilities are maximal in Choquet order; the dominating measure is unrestricted. -/
theorem reference33_choquetMaximality (b : HilbertBasis I ℂ H)
    (mu : ProbabilityMeasure (rankStates b 1)) (nu : ProbabilityMeasure (QuantumState b))
    (hdom : ChoquetDominates b (nu : Measure _)
      (Measure.map (fun rho : rankStates b 1 => rho.val) (mu : Measure _))) :
    (nu : Measure _) = Measure.map (fun rho : rankStates b 1 => rho.val) (mu : Measure _) := by sorry

end Statements

end Operators

end QAlgorithms.Papers.Independent.Support50.P34

end
