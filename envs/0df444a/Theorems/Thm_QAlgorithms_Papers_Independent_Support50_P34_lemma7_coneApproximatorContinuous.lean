-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P34_lemma7_coneApproximatorContinuous
-- name    : QAlgorithms.Papers.Independent.Support50.P34.lemma7_coneApproximatorContinuous
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:47:11.494431+00:00
-- url     : https://prove2.me/theorems/e5805bfc-8815-4a27-876a-8726192dca02
-- title:
--   Lemma 7: continuity of cone entropy approximators
-- statement:
--   For an integer $k\ge1$ and a positive trace-class operator $A$, define the cone approximator using all countable positive rank-at-most-$k$ ensembles with trace-norm average $A$:
--
--   $$H_k(A)=\sup_{\{\pi_i,A_i\}:\,\sum_i\pi_iA_i=A}\sum_i\pi_iH(A_i).$$
--
--   Then $H_k$ is finite and continuous on the entire positive trace-class cone in trace norm, including its zero operator. This supplies continuous approximants on the unnormalized domain.
-- source:
--   Continuity of the von Neumann entropy, arXiv:0904.1963v3, PDF p. 18, Lemma 7: continuity of cone entropy approximators

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

/-- Lemma 7, arXiv:0904.1963v3, PDF p.18: cone approximators are finite and
trace-norm continuous, including the zero operator. -/
theorem lemma7_coneApproximatorContinuous (b : HilbertBasis I ℂ H)
    (k : ℕ) (hk : 0 < k) :
    FiniteEntropyContinuousOn (coneApproximator b k) Set.univ := by sorry

end Statements

end Operators

end QAlgorithms.Papers.Independent.Support50.P34

end
