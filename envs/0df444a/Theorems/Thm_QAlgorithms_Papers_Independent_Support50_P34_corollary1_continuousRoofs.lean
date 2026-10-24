-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P34_corollary1_continuousRoofs
-- name    : QAlgorithms.Papers.Independent.Support50.P34.corollary1_continuousRoofs
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:41:52.617677+00:00
-- url     : https://prove2.me/theorems/b718502d-4657-4662-8d9c-5c83cc4dd2d0
-- title:
--   Corollary 1: continuous bounded rank roofs
-- statement:
--   Let $k\ge1$ and let $f$ be a finite-valued continuous bounded function on $S_k(\mathcal H)$, with the trace-norm topology. The countable and integral concave roofs agree:
--
--   $$\hat f_k^\sigma=\hat f_k^\mu\in C(S(\mathcal H)).$$
--
--   Continuity here includes finiteness. The roofs use respectively all countably atomic and all Borel probability decompositions into states of rank at most $k$. This extends bounded continuous rank-stratum data continuously to all states.
-- source:
--   Continuity of the von Neumann entropy, arXiv:0904.1963v3, PDF p. 13, Corollary 1: continuous bounded rank roofs

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

/-- Corollary 1, arXiv:0904.1963v3, PDF p.13: bounded continuous rank roofs. -/
theorem corollary1_continuousRoofs (b : HilbertBasis I ℂ H) (k : ℕ) (hk : 0 < k)
    (f : rankStates b k → EReal) (hf : FiniteERealContinuousOn f Set.univ)
    (hl : LowerBounded f) (hu : UpperBounded f) :
    sigmaRoof b (rankStates b k) f = upperRoof b (rankStates b k) f ∧
    FiniteERealContinuousOn (upperRoof b (rankStates b k) f) Set.univ := by sorry

end Statements

end Operators

end QAlgorithms.Papers.Independent.Support50.P34

end
