-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P34_proposition3_concaveApproximation
-- name    : QAlgorithms.Papers.Independent.Support50.P34.proposition3_concaveApproximation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:42:37.410979+00:00
-- url     : https://prove2.me/theorems/eca05326-a795-4a42-b94e-512a9ede7424
-- title:
--   Proposition 3 (A–B): approximation of concave functions
-- statement:
--   Let $f:S(\mathcal H)\to[-\infty,+\infty]$ be concave, lower semicontinuous, and lower bounded. A state symmetry means an affine homeomorphism preserving rank strata. For every $k\ge1$, the countable and integral rank roofs agree, are concave and lower semicontinuous, inherit every such symmetry of $f$, and agree with $f$ on $S_k(\mathcal H)$. Moreover,
--
--   $$\hat f_k^\sigma=\hat f_k^\mu\nearrow f\quad\text{pointwise on }S(\mathcal H).$$
--
--   If $f$ has a finite continuous restriction to every $S_k(\mathcal H)$, all these roofs are finite continuous bounded functions. This is the symmetry-preserving approximation theorem; invariance under all unitaries is not imposed as an extra hypothesis.
-- source:
--   Continuity of the von Neumann entropy, arXiv:0904.1963v3, PDF p. 14, Proposition 3 (A–B): approximation of concave functions

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

/-- Proposition 3 A–B, arXiv:0904.1963v3, PDF p.14: all ranks, inherited symmetry,
agreement, monotonicity, pointwise limit, and the separate continuity implication. -/
theorem proposition3_concaveApproximation (b : HilbertBasis I ℂ H)
    (f : QuantumState b → EReal) (hf : LowerSemicontinuous f) (hb : LowerBounded f)
    (hc : StateConcaveOn b Set.univ f) :
    (∀ k : ℕ, 0 < k → rankSigmaRoof b f k = rankMuRoof b f k ∧
      StateConcaveOn b Set.univ (rankMuRoof b f k) ∧
      LowerSemicontinuous (rankMuRoof b f k) ∧
      (∀ rho ∈ rankStates b k, rankMuRoof b f k rho = f rho) ∧
      (∀ S : StateSymmetry b, (∀ rho, f (S.map rho) = f rho) →
        ∀ rho, rankMuRoof b f k (S.map rho) = rankMuRoof b f k rho)) ∧
    (∀ rho, Monotone (fun n : ℕ => rankMuRoof b f (n + 1) rho) ∧
      Tendsto (fun n : ℕ => rankMuRoof b f (n + 1) rho) atTop (nhds (f rho))) ∧
    ((∀ k : ℕ, 0 < k → FiniteERealContinuousOn f (rankStates b k)) →
      ∀ k : ℕ, 0 < k → FiniteERealContinuousOn (rankMuRoof b f k) Set.univ ∧
        LowerBounded (rankMuRoof b f k) ∧ UpperBounded (rankMuRoof b f k)) := by sorry

end Statements

end Operators

end QAlgorithms.Papers.Independent.Support50.P34

end
