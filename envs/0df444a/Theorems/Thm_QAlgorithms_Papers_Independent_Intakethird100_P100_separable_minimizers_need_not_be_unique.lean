-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P100_separable_minimizers_need_not_be_unique
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P100.separable_minimizers_need_not_be_unique
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:27:43.4442+00:00
-- url     : https://prove2.me/theorems/aac0b109-f2b6-40b9-8e8d-1c9c3a3c6508
-- title:
--   Closest separable states need not be unique
-- statement:
--   There exist positive finite local dimensions and a bipartite density matrix $\sigma$ having two distinct separable minimizers $\rho_1,\rho_2$. Here separable means a finite convex combination of product density matrices, and $E_r$ is the infimum of support-aware Umegaki relative entropy in natural logarithms over exactly those normalized states. More precisely,
--
--   $$
--   \rho_1\neq\rho_2,\qquad E_r(\sigma)<\infty,\qquad
--   S(\sigma\Vert\rho_1)=S(\sigma\Vert\rho_2)=E_r(\sigma).
--   $$
--
--   This shows why a closest separable state cannot in general be treated as a uniquely defined state.
--
--   **Formalization Note** The accepted infimum and its attaining comparisons are stored in bits. Multiplication by the positive constant $\log 2$ gives the natural-logarithm values and preserves finiteness and every minimizing equality.
-- source:
--   Continuity of Relative Entropy of Entanglement, arXiv:quant-ph/9910002v1, PDF p. 3, Final discussion before the Corollary

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P100

noncomputable section

open Filter

open scoped ENNReal Topology ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakethird100.P100

open QAlgorithms.Papers.Independent.Dependency50.P15
  (relativeDistance relativeDistanceValue positiveOperatorRelativeEntropyBits groupedTensorPower)

open QAlgorithms.Papers.Independent.Information100.P54
  (relativeEntropyBits relativeEntanglement)

/-- Final discussion, PDF p.3: some bipartite state has two distinct closest
separable states. The positive finite local dimensions are existential, with
no unsupported assertion that this occurs for every state or every dimension. -/
theorem separable_minimizers_need_not_be_unique :
    ∃ a b : ℕ,
      ∃ sigma rhoOne rhoTwo :
        Matrix (Fin (a + 1) × Fin (b + 1)) (Fin (a + 1) × Fin (b + 1)) ℂ,
      IsDensityMatrix sigma ∧
      rhoOne ∈ separableStates ∧ rhoTwo ∈ separableStates ∧ rhoOne ≠ rhoTwo ∧
      relativeEntanglement sigma < ⊤ ∧
      relativeEntropyBits sigma rhoOne = relativeEntanglement sigma ∧
      relativeEntropyBits sigma rhoTwo = relativeEntanglement sigma := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P100

end
