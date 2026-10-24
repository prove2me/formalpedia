-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P34_corollary2_uniformApproximation
-- name    : QAlgorithms.Papers.Independent.Support50.P34.corollary2_uniformApproximation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:45:11.091393+00:00
-- url     : https://prove2.me/theorems/ab3d6eb5-5265-4c8c-97da-985a3199770e
-- title:
--   Corollary 2 (A–B): uniform approximation and continuity
-- statement:
--   Let $f$ be a concave lower semicontinuous lower-bounded extended-real function on $S(\mathcal H)$, and let $A\subseteq S(\mathcal H)$.
--
--   1. If $f$ is finite continuous on every rank stratum and its rank roofs converge uniformly on $A$, then $f$ is finite continuous on $A$.
--   2. If $A$ is compact and $f$ is finite continuous on $A$, the rank roofs converge uniformly there.
--
--   $$\hat f_k^\sigma=\hat f_k^\mu\longrightarrow f\quad\text{uniformly on }A.$$
--
--   Uniform approximation uses the two additive extended-real inequalities with arbitrary positive real tolerance. The second assertion does not require rank-stratum continuity. This is the continuity criterion used for entropy.
-- source:
--   Continuity of the von Neumann entropy, arXiv:0904.1963v3, PDF p. 15, Corollary 2 (A–B): uniform approximation and continuity

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

/-- Corollary 2 A–B, arXiv:0904.1963v3, PDF p.15: uniform approximation
and the compact converse, without carrying the hypotheses of A into B. -/
theorem corollary2_uniformApproximation (b : HilbertBasis I ℂ H)
    (f : QuantumState b → EReal) (hf : LowerSemicontinuous f) (hb : LowerBounded f)
    (hc : StateConcaveOn b Set.univ f) (A : Set (QuantumState b)) :
    ((∀ k : ℕ, 0 < k → FiniteERealContinuousOn f (rankStates b k)) →
      UniformExtendedApproximation (fun n => rankMuRoof b f (n + 1)) f A →
      FiniteERealContinuousOn f A) ∧
    (IsCompact A → FiniteERealContinuousOn f A →
      UniformExtendedApproximation (fun n => rankMuRoof b f (n + 1)) f A) := by sorry

end Statements

end Operators

end QAlgorithms.Papers.Independent.Support50.P34

end
