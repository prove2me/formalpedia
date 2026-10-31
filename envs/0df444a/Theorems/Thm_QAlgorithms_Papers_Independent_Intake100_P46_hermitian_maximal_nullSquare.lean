-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P46_hermitian_maximal_nullSquare
-- name    : QAlgorithms.Papers.Independent.Intake100.P46.hermitian_maximal_nullSquare
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:11:06.856699+00:00
-- url     : https://prove2.me/theorems/373fd4a1-984a-4d41-80b1-31a1dc96c0f3
-- title:
--   Maximum totally isotropic dimension of a Hermitian form
-- statement:
--   Let $C$ be a Hermitian matrix on a finite complex coordinate space, allowing dimension zero. Let $n_+,n_-,n_0$ count its positive, negative and zero eigenvalues with algebraic multiplicity. A complex linear subspace $S$ is totally isotropic when $v^\dagger Cw=0$ for every $v,w\in S$. Put $d_C=\min(n_+,n_-)+n_0$. Then
--
--   $$\forall S\text{ totally isotropic},\quad\dim_{\mathbb C}S\le d_C,\qquad\exists S\text{ totally isotropic with }\dim_{\mathbb C}S=d_C.$$
--
--   This gives the size of the largest null-square block achievable by a change of basis, as a bound with attainment. It does not require the subspace to be invariant under $C$ or contained in its kernel.
-- source:
--   A purification postulate for quantum mechanics with indefinite causal order, arXiv:1611.08535v4, PDF p. 12, Appendix D, pp.12–13

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P46

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Intake100.P46

/-- PDF pp.12–13, Appendix D: the upper bound for every totally isotropic complex
subspace and attainment of the full bound, including the empty ambient space.
The final printed A on p.13 denotes C; negative eigenvalues are strictly negative. -/
theorem hermitian_maximal_nullSquare {I : Type*} [Fintype I] [DecidableEq I]
    (C : Matrix I I ℂ) (hC : C.IsHermitian) :
    (∀ S : Submodule ℂ (I → ℂ), IsTotallyIsotropic C S →
      Module.finrank ℂ S ≤ nullSquareSize hC) ∧
    (∃ S : Submodule ℂ (I → ℂ), IsTotallyIsotropic C S ∧
      Module.finrank ℂ S = nullSquareSize hC) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P46

end
