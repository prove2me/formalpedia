-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_full_support_converse
-- name    : QAlgorithms.Papers.Independent.Information100.P62.full_support_converse
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T21:40:42.322192+00:00
-- url     : https://prove2.me/theorems/862255db-9d25-487c-bca4-41744f5f2122
-- title:
--   Lemma 3.11: full-support spectral converse
-- statement:
--   Suppose a transmittable algebra $A=\bigoplus_kM_{d_k}(\mathbb C)$ uses the full input dimension: $\sum_kd_k=\dim H$. Then $S_\Phi$ is commutative. For every self-adjoint $X\in S_\Phi$, there are real labels $\lambda_k$ such that
--   $$\dim\ker(X-tI)=\sum_{k:\lambda_k=t}d_k\quad(t\in\mathbb R).$$
--   Thus every eigenspace multiplicity is obtained by grouping whole block labels, and every label is used. This is the exact coarsening assertion.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 28, Lemma 3.11: full-support spectral converse

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.28, Lemma 3.11: full-support spectral converse. -/
theorem full_support_converse [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) (A : Shape) (hA : Transmits F A)
    (hfull : lengthDim A = Fintype.card I) :
    (∀ X ∈ graph F, ∀ Y ∈ graph F, X * Y = Y * X) ∧
    ∀ X ∈ graph F, X.IsHermitian → ∃ lam : Block A → ℝ, ∀ t : ℝ,
      Module.finrank ℂ (kernelSpace (X - (t : ℂ) • (1 : Matrix I I ℂ))) =
        ∑ k ∈ univ.filter (fun k => lam k = t), blockSize A k := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
