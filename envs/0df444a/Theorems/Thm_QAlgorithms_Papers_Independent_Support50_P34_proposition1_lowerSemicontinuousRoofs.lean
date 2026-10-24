-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P34_proposition1_lowerSemicontinuousRoofs
-- name    : QAlgorithms.Papers.Independent.Support50.P34.proposition1_lowerSemicontinuousRoofs
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:40:20.973439+00:00
-- url     : https://prove2.me/theorems/f80cab9a-8646-4de7-8b51-781ae2b9286e
-- title:
--   Proposition 1: lower semicontinuous rank-concave roofs
-- statement:
--   Let $k\ge1$ and let $f:S_k(\mathcal H)\to[-\infty,+\infty]$ be lower semicontinuous and bounded below by a real number. Its countable concave roof $\hat f_k^\sigma$ maximizes ensemble averages over countable rank-at-most-$k$ decompositions; its integral roof $\hat f_k^\mu$ maximizes extended integrals over all Borel probability decompositions. Then
--
--   $$\hat f_k^\sigma=\hat f_k^\mu.$$
--
--   The common function is lower semicontinuous and $\mu$-concave on all states. Here $\mu$-concavity includes universal completion-measurability and Jensen's inequality for every Borel probability with its specified barycenter. No finite upper bound is assumed. This identifies the two roofs in the lower semicontinuous regime.
-- source:
--   Continuity of the von Neumann entropy, arXiv:0904.1963v3, PDF p. 12, Proposition 1: lower semicontinuous rank-concave roofs

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

/-- Proposition 1, arXiv:0904.1963v3, PDF p.12: equality, lower semicontinuity,
and universal-measurability-inclusive mu concavity. -/
theorem proposition1_lowerSemicontinuousRoofs (b : HilbertBasis I ℂ H)
    (k : ℕ) (hk : 0 < k) (f : rankStates b k → EReal)
    (hf : LowerSemicontinuous f) (hb : LowerBounded f) :
    sigmaRoof b (rankStates b k) f = upperRoof b (rankStates b k) f ∧
    LowerSemicontinuous (upperRoof b (rankStates b k) f) ∧
    MuConcave b (upperRoof b (rankStates b k) f) := by sorry

end Statements

end Operators

end QAlgorithms.Papers.Independent.Support50.P34

end
