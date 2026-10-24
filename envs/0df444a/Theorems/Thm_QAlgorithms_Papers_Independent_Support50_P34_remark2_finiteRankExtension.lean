-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P34_remark2_finiteRankExtension
-- name    : QAlgorithms.Papers.Independent.Support50.P34.remark2_finiteRankExtension
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:44:23.483213+00:00
-- url     : https://prove2.me/theorems/1aa35992-f8d2-427a-9751-5695a2876a44
-- title:
--   Remark 2: unique lower semicontinuous extension from finite-rank states
-- statement:
--   Let $f$ be a concave lower-bounded extended-real function on the finite-rank states $S_f(\mathcal H)$ whose restriction to each $S_k(\mathcal H)$ is lower semicontinuous. There exists a unique lower-bounded concave lower semicontinuous extension $g$ to all states, given by
--
--   $$g(\rho)=\sup_{k\ge1}\hat f_k^\sigma(\rho)=\sup_{k\ge1}\hat f_k^\mu(\rho).$$
--
--   Every rank-preserving affine state-space symmetry of $f$ is inherited by $g$. If $f$ is nonnegative then $g$ is nonnegative; in particular the construction preserves entropy-type properties, including unitary invariance when present. Uniqueness ranges over all lower-bounded concave lower semicontinuous extensions. This supplies both construction and uniqueness, not a freely supplied extension premise.
-- source:
--   Continuity of the von Neumann entropy, arXiv:0904.1963v3, PDF p. 15, Remark 2: unique lower semicontinuous extension from finite-rank states

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

/-- Remark 2, arXiv:0904.1963v3, PDF p.15: existence, explicit roof formulas,
symmetry inheritance, and uniqueness among all lower-bounded lsc concave extensions.
Only values of f on finite-rank states enter any premise or construction. -/
theorem remark2_finiteRankExtension (b : HilbertBasis I ℂ H)
    (f : QuantumState b → EReal)
    (hb : ∃ c : ℝ, ∀ rho ∈ finiteRankStates b, (c : EReal) ≤ f rho)
    (hc : StateConcaveOn b (finiteRankStates b) f)
    (hlsc : ∀ k : ℕ, 0 < k →
      LowerSemicontinuous (fun rho : rankStates b k => f rho.val)) :
    ∃ g : QuantumState b → EReal,
      LowerSemicontinuous g ∧ LowerBounded g ∧ StateConcaveOn b Set.univ g ∧
      (∀ rho ∈ finiteRankStates b, g rho = f rho) ∧
      (∀ rho, g rho = ⨆ n : ℕ, rankSigmaRoof b f (n + 1) rho) ∧
      (∀ rho, g rho = ⨆ n : ℕ, rankMuRoof b f (n + 1) rho) ∧
      (∀ S : StateSymmetry b,
        (∀ rho ∈ finiteRankStates b, f (S.map rho) = f rho) →
        ∀ rho, g (S.map rho) = g rho) ∧
      ((∀ rho ∈ finiteRankStates b, 0 ≤ f rho) → ∀ rho, 0 ≤ g rho) ∧
      (∀ g' : QuantumState b → EReal, LowerSemicontinuous g' → LowerBounded g' →
        StateConcaveOn b Set.univ g' →
        (∀ rho ∈ finiteRankStates b, g' rho = f rho) → g' = g) := by sorry

end Statements

end Operators

end QAlgorithms.Papers.Independent.Support50.P34

end
