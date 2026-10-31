-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P48_abelianTotalDimension
-- name    : QAlgorithms.Papers.Independent.Intake100.P48.abelianTotalDimension
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:27:02.190664+00:00
-- url     : https://prove2.me/theorems/6bd58ede-e042-47ab-8383-2883c1374bb9
-- title:
--   Total quantum dimension for abelian sectors
-- statement:
--   Let $\mathcal A$ be a finite nonempty set of abelian superselection sectors, with quantum dimensions $d_a=1$ for every $a\in\mathcal A$. Define $D=(\sum_{a\in\mathcal A}d_a^2)^{1/2}$. Then
--
--   $$
--   D^2=|\mathcal A|.
--   $$
--
--   This is the numerical specialization of total quantum dimension; the fact that an abelian sector has dimension one is the stated input.
-- source:
--   Topological entanglement entropy, arXiv:hep-th/0510092v2, PDF p. 1, Text below Eq. (3)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P48

open Filter

open scoped Topology ComplexConjugate

attribute [local instance] Classical.propDecidable

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- PDF p.1, below (3): in the all-abelian case every quantum dimension is 1,
so the square of the total quantum dimension counts all superselection sectors. -/
theorem abelianTotalDimension [Nonempty A] (dim : A → ℝ)
    (habelian : ∀ a, dim a = 1) :
    totalDimension dim ^ 2 = (Fintype.card A : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P48

end
