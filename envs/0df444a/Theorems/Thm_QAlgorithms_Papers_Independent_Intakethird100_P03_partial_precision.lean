-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P03_partial_precision
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P03.partial_precision
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:56:08.192604+00:00
-- url     : https://prove2.me/theorems/3c5a0081-4758-49b8-9177-450db32d29a9
-- title:
--   §2.4.2: inverse and composition of partial-unitary approximations
-- statement:
--   For partial unitaries, inversion preserves the source precision relation, including both domain and range inclusions. For two compatible chains with component precisions δ_j ≥ 0, specify initial domains N ⊆ Ntilde on which both chains are valid. In addition, require that the image of N under the exact composite is contained in the image of Ntilde under the approximate composite. Then the composites satisfy the full precision relation with precision ∑_j δ_j: both inclusions and the uniform vector bound ‖V_comp x − U_comp x‖ ≤ (∑_j δ_j)‖x‖ on N. The empty chain is the identity. The final-range assumption corrects a defect in the source extension; compatibility and factorwise range inclusions alone do not imply it.
-- source:
--   Quantum measurements and the Abelian Stabilizer Problem, arXiv:quant-ph/9511026v1, PDF p. 12, §2.4.2: inverse and composition of partial-unitary approximations

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P03

noncomputable section

open scoped Matrix ComplexConjugate Kronecker

namespace QAlgorithms.Papers.Independent.Intakethird100.P03

open QAlgorithms.Papers.Independent.Renew46.P01 (cleanVector)

attribute [local instance] Classical.propDecidable

/-- PDF p.12: inversion preserves precision. Source correction for composition:
printed "Lemma 3 remains valid for partial unitary operators" omits a necessary
composite-range inclusion. We require that inclusion explicitly, while retaining
both component inclusions, valid chains and the full precision conclusion.
Reason: I on a line followed by I versus a small full-space rotation has close
factors but distinct composite range lines. Inversion is unchanged. -/
theorem partial_precision {I : Type*} [Fintype I] :
    (∀ (U V : PartialUnitary I) (d : ℝ), 0 ≤ d → PartialApprox V U d →
      PartialApprox V.inverse U.inverse d) ∧
    (∀ (L : ℕ) (U V : Fin L → PartialUnitary I) (d : Fin L → ℝ)
      (N Ntilde : Submodule ℂ (EuclideanSpace ℂ I)),
      (∀ j, 0 ≤ d j) → (∀ j, PartialApprox (V j) (U j) (d j)) →
      N ≤ Ntilde →
      (∀ j : Fin L, j.val = 0 → N ≤ (U j).domain) →
      (∀ j : Fin L, j.val = 0 → Ntilde ≤ (V j).domain) →
      (∀ i j : Fin L, j.val = i.val + 1 → (U i).range ≤ (U j).domain) →
      (∀ i j : Fin L, j.val = i.val + 1 → (V i).range ≤ (V j).domain) →
      (∀ x ∈ N, ∃ y ∈ Ntilde,
        partialRun (List.ofFn U) x = partialRun (List.ofFn V) y) →
      PartialSequenceApprox (List.ofFn V) (List.ofFn U) N Ntilde (∑ j, d j)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P03

end
