-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P98_three_part_exchange_symmetry
-- name    : QAlgorithms.Papers.Independent.Intake100.P98.three_part_exchange_symmetry
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:09:33.904109+00:00
-- url     : https://prove2.me/theorems/9cc72a72-bc15-4f3c-a313-cdeb85e3a158
-- title:
--   Remark 5.1: exchange symmetry of the explicit LR_3 complex
-- statement:
--   Let $\lambda,\mu,\nu$ be partitions with at most three parts, padded by zeros. Define $S(\lambda,\mu,\nu)=(\mu,\lambda,\nu)$. Then
--
--   $$
--   c^\nu_{\lambda\mu}=c^\nu_{\mu\lambda},\qquad
--   C\in\mathrm{LR}_3\ \Longrightarrow\ S(C)\in\mathrm{LR}_3.
--   $$
--
--   Here $\mathrm{LR}_3$ is the complex actually constructed from the hive matrix, not a freely selected subdivision. The second assertion retains the geometric symmetry, independently of the defective numerical entries in the printed table.
-- source:
--   A polynomiality property for Littlewood-Richardson coefficients, arXiv:math/0308101v2, PDF p. 13, Remark 5.1: exchange symmetry of the explicit LR_3 complex

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P98

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P98

open QAlgorithms.Papers.Independent.Frontier30.P19

attribute [local instance] Classical.propDecidable

/-- Remark 5.1, PDF p.13: coefficient symmetry AND geometric symmetry of
this constructed LR_3 complex. Coefficient symmetry is for all partition
triples; the geometric clause has the LR domain through lrComplex.
No defective numerical table entry is used. -/
theorem three_part_exchange_symmetry :
    (∀ x : Coordinates 3 → ℕ, (∀ b : Fin 3, Antitone (fun i => x (b,i))) →
      paddedLRCoefficient x = paddedLRCoefficient (exchangeLRBlocks x)) ∧
    (∀ C ∈ lrComplex 3, exchangeLRBlocks '' C ∈ lrComplex 3) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P98

end
