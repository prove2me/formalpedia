-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P34_proposition2_upperSemicontinuousRoof
-- name    : QAlgorithms.Papers.Independent.Support50.P34.proposition2_upperSemicontinuousRoof
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:41:17.414975+00:00
-- url     : https://prove2.me/theorems/adf3ef59-7a3a-4ba1-80cd-dd343bc9fd01
-- title:
--   Proposition 2: upper semicontinuous rank-concave roof and attainment
-- statement:
--   Let $k\ge1$ and let $f:S_k(\mathcal H)\to[-\infty,+\infty]$ be upper semicontinuous and bounded above by a real number. Its integral concave roof satisfies
--
--   $$\hat f_k^\mu(\rho)=\max_{\mu\in\mathcal P_\rho(S_k(\mathcal H))}\int f\,d\mu.$$
--
--   It is upper semicontinuous and $\mu$-concave on $S(\mathcal H)$, where $\mu$-concavity includes universal completion-measurability. This gives attainment for every state without asserting equality with the countable roof.
-- source:
--   Continuity of the von Neumann entropy, arXiv:0904.1963v3, PDF p. 13, Proposition 2: upper semicontinuous rank-concave roof and attainment

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

/-- Proposition 2, arXiv:0904.1963v3, PDF p.13: upper semicontinuous mu roof,
with supremum attainment; no equality with the sigma roof is asserted. -/
theorem proposition2_upperSemicontinuousRoof (b : HilbertBasis I ℂ H)
    (k : ℕ) (hk : 0 < k) (f : rankStates b k → EReal)
    (hf : UpperSemicontinuous f) (hb : UpperBounded f) :
    UpperSemicontinuous (upperRoof b (rankStates b k) f) ∧
    MuConcave b (upperRoof b (rankStates b k) f) ∧
    ∀ rho : QuantumState b, ∃ mu ∈ stateFiber b (rankStates b k) rho,
      upperRoof b (rankStates b k) f rho = extendedIntegral (mu : Measure _) f := by sorry

end Statements

end Operators

end QAlgorithms.Papers.Independent.Support50.P34

end
