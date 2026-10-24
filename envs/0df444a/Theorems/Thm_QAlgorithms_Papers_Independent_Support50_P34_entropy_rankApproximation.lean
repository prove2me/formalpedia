-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P34_entropy_rankApproximation
-- name    : QAlgorithms.Papers.Independent.Support50.P34.entropy_rankApproximation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:45:45.1949+00:00
-- url     : https://prove2.me/theorems/cee7fe7e-1e6b-4a93-bb8b-6a6844b85fce
-- title:
--   §5 unnumbered: von Neumann entropy approximators
-- statement:
--   For a separable complex Hilbert space, the von Neumann entropy $H(\rho)=-\operatorname{Tr}\rho\log\rho\in[0,+\infty]$ is concave, lower semicontinuous and unitarily invariant, and finite continuous on every $S_k(\mathcal H)$, $k\ge1$. For Borel probabilities $\mu$ with barycenter $\rho$ supported on $S_k$, and their countably atomic subfamily, define
--
--   $$H_k(\rho)=\sup_{\{\pi_i,\rho_i\}}\sum_i\pi_iH(\rho_i)=\sup_{\mu\in\mathcal P_\rho(S_k)}\int H(\sigma)\,d\mu.$$
--
--   The functions $H_k$ are nonnegative concave finite continuous bounded and unitarily invariant, satisfy $H_k\le\log k$, agree with $H$ on $S_k$, and increase pointwise to $H$. For the extended relative entropy $D$, both defect formulas hold:
--
--   $$H(\rho)-H_k(\rho)=\inf_{\{\pi_i,\rho_i\}}\sum_i\pi_iD(\rho_i\Vert\rho)=\inf_{\mu\in\mathcal P_\rho(S_k)}\int D(\sigma\Vert\rho)\,d\mu.$$
--
--   All logarithms are natural. These are the rank entropy approximators and their relative-entropy errors. **Formalization Note** The valid dimension-independent bound replaces footnote 14's full-range assertion; that correction requires independent moderation.
-- source:
--   Continuity of the von Neumann entropy, arXiv:0904.1963v3, PDF p. 16, §5 unnumbered: von Neumann entropy approximators

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

/-- Section 5 unnumbered result, arXiv:0904.1963v3, PDF p.16: both entropy roofs
and both relative-entropy defect infima, plus the stated analytical properties.
The footnote's dimension-dependent full-range claim is replaced by the planned
valid upper bound log k; no finite-dimensional state space has all infinite entropies. -/
theorem entropy_rankApproximation (b : HilbertBasis I ℂ H) :
    LowerSemicontinuous (stateEntropyExt b) ∧
    StateConcaveOn b Set.univ (stateEntropyExt b) ∧
    StateUnitaryInvariant b (stateEntropyExt b) ∧
    (∀ k : ℕ, 0 < k → FiniteERealContinuousOn (stateEntropyExt b) (rankStates b k)) ∧
    (∀ k : ℕ, 0 < k →
      rankSigmaRoof b (stateEntropyExt b) k = rankMuRoof b (stateEntropyExt b) k ∧
      StateConcaveOn b Set.univ (rankMuRoof b (stateEntropyExt b) k) ∧
      FiniteERealContinuousOn (rankMuRoof b (stateEntropyExt b) k) Set.univ ∧
      StateUnitaryInvariant b (rankMuRoof b (stateEntropyExt b) k) ∧
      (∀ rho, 0 ≤ rankMuRoof b (stateEntropyExt b) k rho ∧
        rankMuRoof b (stateEntropyExt b) k rho ≤ (Real.log (k : ℝ) : EReal)) ∧
      (∀ rho ∈ rankStates b k, rankMuRoof b (stateEntropyExt b) k rho = stateEntropyExt b rho) ∧
      (∀ rho, stateEntropy b rho - (rankMuRoof b (stateEntropyExt b) k rho).toENNReal =
        stateRelativeDefect b k true rho ∧
        stateEntropy b rho - (rankMuRoof b (stateEntropyExt b) k rho).toENNReal =
        stateRelativeDefect b k false rho)) ∧
    (∀ rho, Monotone (fun n : ℕ => rankMuRoof b (stateEntropyExt b) (n + 1) rho) ∧
      Tendsto (fun n : ℕ => rankMuRoof b (stateEntropyExt b) (n + 1) rho)
        atTop (nhds (stateEntropyExt b rho))) := by sorry

end Statements

end Operators

end QAlgorithms.Papers.Independent.Support50.P34

end
