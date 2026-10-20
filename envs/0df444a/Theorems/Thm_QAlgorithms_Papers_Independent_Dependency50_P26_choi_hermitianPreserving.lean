-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P26_choi_hermitianPreserving
-- name    : QAlgorithms.Papers.Independent.Dependency50.P26.choi_hermitianPreserving
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T14:26:57.632604+00:00
-- url     : https://prove2.me/theorems/3e469c6b-d612-4d5e-b788-d61296722487
-- title:
--   Lemma 2: Hermitian preservation
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces of positive dimension with fixed orthonormal bases. Let $\mathcal M:L(H_0)\to L(H_1)$ be complex-linear. It maps every Hermitian operator to a Hermitian operator if and only if its output-first Choi operator is Hermitian:
--
--   $$
--   \mathcal M\text{ preserves Hermiticity}\quad\Longleftrightarrow\quad C(\mathcal M)^\dagger=C(\mathcal M).
--   $$
--
--   Relates the real structure of a superoperator to its Choi matrix.
-- source:
--   Theoretical framework for quantum networks, arXiv:0904.4483v2, PDF p. 2, Lemma 2: Hermitian preservation

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P26

/-- PDF p.2, Lemma 2. -/
theorem choi_hermitianPreserving {I O : Type*} [Fintype I] [Fintype O]
    [Nonempty I] [Nonempty O] (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    HermitianPreserving M ↔ (outputFirstChoi M).IsHermitian := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P26

end
