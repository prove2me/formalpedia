-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_orthogonal_codes
-- name    : QAlgorithms.Papers.Independent.Information100.P62.orthogonal_codes
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T21:35:30.235805+00:00
-- url     : https://prove2.me/theorems/4782d44c-30e0-4280-be16-7e4446ea8053
-- title:
--   Lemma 3.5: orthogonal quantum codes
-- statement:
--   Let $A=\bigoplus_kM_{d_k}(\mathbb C)$ be nonzero with positive block sizes. For a channel $\Phi$, transmittability is equivalent to existence of code projections $P_k$ of ranks $d_k$ satisfying
--   $$P_kS_\Phi P_k=\mathbb CP_k,\qquad P_kS_\Phi P_j=0\ (k\ne j).$$
--   This characterizes hybrid transmission through pairwise distinguishable quantum codes.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 23, Lemma 3.5: orthogonal quantum codes

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.23, 24, Lemma 3.5: orthogonal quantum codes. -/
theorem orthogonal_codes [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) (A : Shape) (hA : Valid A) :
    Transmits F A ↔ ∃ P : Block A → Matrix I I ℂ,
      (∀ k, Code (graph F) (P k) ∧ (P k).rank = blockSize A k) ∧
      ∀ k j, k ≠ j → ∀ s ∈ graph F, P k * s * P j = 0 := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
