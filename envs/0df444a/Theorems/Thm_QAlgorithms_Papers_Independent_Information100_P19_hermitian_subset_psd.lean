-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_hermitian_subset_psd
-- name    : QAlgorithms.Papers.Independent.Information100.P19.hermitian_subset_psd
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:43:25.62898+00:00
-- url     : https://prove2.me/theorems/49a54c1e-b864-4154-a98b-ea5085b2704a
-- title:
--   Proposition 3.2
-- statement:
--   For every degree $n\ge1$,
--   $$I_n^{\rm all}\subseteq I_n^{\rm psd}.$$
--   The inclusion is strict in degrees two and four: $[1^2]-[2]$ and $[31]-[22]$ are PSD-valid and are not all-Hermitian-valid. This asserts the source's illustrative strictness, without claiming strictness in every degree.
--
--   For a partition $\lambda$, the symbol $[\lambda]$ denotes a formal basis element evaluated as $\prod_j\operatorname{Tr}(X^{\lambda_j})$. Distinct formal coefficients are not identified by any fixed-dimensional trace identity.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 12, Proposition 3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Proposition 3.2; arXiv:2609.29471v1, PDF pp.12. -/
theorem hermitian_subset_psd (n : ℕ) (hn : 1 ≤ n) :
    allCone n ⊆ psdCone n ∧
    b11-b2 ∈ psdCone 2 ∧ b11-b2 ∉ allCone 2 ∧
    b31-b22 ∈ psdCone 4 ∧ b31-b22 ∉ allCone 4 := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
