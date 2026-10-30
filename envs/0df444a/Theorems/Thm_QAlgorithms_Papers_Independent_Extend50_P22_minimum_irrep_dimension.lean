-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P22_minimum_irrep_dimension
-- name    : QAlgorithms.Papers.Independent.Extend50.P22.minimum_irrep_dimension
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:22:35.769033+00:00
-- url     : https://prove2.me/theorems/3ee01757-b84f-47b1-b5fd-ce27fbf535fb
-- title:
--   Lemma 16: minimum irrep dimension at fixed first row
-- statement:
--   Let $d\ge1$ and $\lambda_1\ge\cdots\ge\lambda_d=0$ be nonnegative integer highest weights. Define the actual irrep dimension by the Weyl product $D_\lambda=\prod_{i<j}(\lambda_i-\lambda_j+j-i)/(j-i)$. Then $$D_{(\lambda_1,0,\ldots,0)}=\binom{d-1+\lambda_1}{d-1}\le D_\lambda.$$ The normalization removes determinant shifts, and no uniqueness of a minimizing representation is claimed.
-- source:
--   Continuous symmetries and approximate quantum error correction, arXiv:1902.07714v1, PDF p. 55, Lemma 16: minimum irrep dimension at fixed first row

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P22

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible)

open QAlgorithms.Papers.Independent.Renew46.P45 (symmetricWeight)

/-- PDF pp.55–56, Lemma 16. Normalization lambda_d=0 excludes determinant shifts.
No uniqueness of a minimizer is asserted. -/
theorem minimum_irrep_dimension (d : ℕ) (hd : 0 < d) (lambda : Fin d → ℕ)
    (hmono : Antitone lambda) (hlast : lambda ⟨d - 1, by omega⟩ = 0) :
    normalizedWeylDimension (symmetricRows d (lambda ⟨0, hd⟩)) =
      (Nat.choose (d - 1 + lambda ⟨0, hd⟩) (d - 1) : ℝ) ∧
    (Nat.choose (d - 1 + lambda ⟨0, hd⟩) (d - 1) : ℝ) ≤ normalizedWeylDimension lambda := by sorry

end QAlgorithms.Papers.Independent.Extend50.P22

end
