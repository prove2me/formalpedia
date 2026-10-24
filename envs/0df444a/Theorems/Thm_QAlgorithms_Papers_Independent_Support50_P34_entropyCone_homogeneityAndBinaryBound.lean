-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P34_entropyCone_homogeneityAndBinaryBound
-- name    : QAlgorithms.Papers.Independent.Support50.P34.entropyCone_homogeneityAndBinaryBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:46:37.090986+00:00
-- url     : https://prove2.me/theorems/3d682248-4198-4a28-9027-68a08a6d04aa
-- title:
--   §5.1 unnumbered: homogeneity and binary entropy bound (2)–(3)
-- statement:
--   For positive trace-class operators use the homogeneous quantum entropy $H(A)=-\operatorname{Tr}A\log A-\eta(\operatorname{Tr}A)$, where $\eta(x)=-x\log x$ and $\eta(0)=0$. For $\lambda\ge0$ and $0\le A\le B$,
--
--   $$H(\lambda A)=\lambda H(A),$$
--
--   $$H(A)+H(B-A)\le H(B)\le H(A)+H(B-A)+\operatorname{Tr}B\,h_2\!\left(\frac{\operatorname{Tr}A}{\operatorname{Tr}B}\right),$$
--
--   where $h_2(x)=\eta(x)+\eta(1-x)$. The perspective term is zero at $A=B=0$, and zero times infinite entropy is zero. This is the homogeneous extension used on the full positive cone, with natural logarithms.
-- source:
--   Continuity of the von Neumann entropy, arXiv:0904.1963v3, PDF p. 17, §5.1 unnumbered: homogeneity and binary entropy bound (2)–(3)

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

/-- Section 5.1, (2)–(3), arXiv:0904.1963v3, PDF p.17: homogeneous entropy
and both inequalities, with the binary perspective taking zero at trace zero. -/
theorem entropyCone_homogeneityAndBinaryBound (b : HilbertBasis I ℂ H) :
    (∀ (A : PositiveCone H) (lam : ℝ), 0 ≤ lam →
      coneEntropyRaw b ((lam : ℂ) • coneOp A) = ENNReal.ofReal lam * coneEntropy b A) ∧
    (∀ A B : PositiveCone H, IsPositive (coneOp B - coneOp A) →
      coneEntropy b A + coneEntropyRaw b (coneOp B - coneOp A) ≤ coneEntropy b B ∧
      coneEntropy b B ≤ coneEntropy b A + coneEntropyRaw b (coneOp B - coneOp A) +
        ENNReal.ofReal ((operatorTrace b (coneOp B)).re) *
          binaryEntropy ((operatorTrace b (coneOp A)).re / (operatorTrace b (coneOp B)).re)) := by sorry

end Statements

end Operators

end QAlgorithms.Papers.Independent.Support50.P34

end
