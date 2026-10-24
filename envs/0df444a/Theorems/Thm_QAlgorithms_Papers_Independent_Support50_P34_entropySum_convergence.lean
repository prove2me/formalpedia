-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P34_entropySum_convergence
-- name    : QAlgorithms.Papers.Independent.Support50.P34.entropySum_convergence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:48:49.94221+00:00
-- url     : https://prove2.me/theorems/42eb8cfd-c1eb-455e-b162-940145c8d702
-- title:
--   §5.2 unnumbered: entropy convergence of sums
-- statement:
--   Let $A_n\to A_0$ and $B_n\to B_0$ be trace-norm convergent sequences of positive trace-class operators. With the paper's convention that an entropy continuity limit has a finite limiting value,
--
--   $$\{H(A_n+B_n)\to H(A_0+B_0)<\infty\}\ \Longleftrightarrow\ \{H(A_n)\to H(A_0)<\infty\}\ \land\ \{H(B_n)\to H(B_0)<\infty\}.$$
--
--   Entropy is the homogeneous cone entropy. No finiteness of all early sequence values is required. This is the continuity-based sum equivalence; it does not assert the unrestricted extended-infinity version.
-- source:
--   Continuity of the von Neumann entropy, arXiv:0904.1963v3, PDF p. 29, §5.2 unnumbered: entropy convergence of sums

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

/-- Section 5.2 unnumbered equivalence, arXiv:0904.1963v3, PDF p.29.
The source's p.7 finite-valued continuity convention is applied to every arrow. -/
theorem entropySum_convergence (b : HilbertBasis I ℂ H)
    (u v : ℕ → PositiveCone H) (A B : PositiveCone H)
    (hu : Tendsto u atTop (nhds A)) (hv : Tendsto v atTop (nhds B)) :
    EntropyConverges b (fun n => coneOp (u n) + coneOp (v n)) (coneOp A + coneOp B) ↔
      EntropyConverges b (fun n => coneOp (u n)) (coneOp A) ∧
      EntropyConverges b (fun n => coneOp (v n)) (coneOp B) := by sorry

end Statements

end Operators

end QAlgorithms.Papers.Independent.Support50.P34

end
