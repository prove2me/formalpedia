-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P17_pure_operation_characterization
-- name    : QAlgorithms.Papers.Independent.Support21.P17.pure_operation_characterization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:40:29.641833+00:00
-- url     : https://prove2.me/theorems/bc9a4bda-cd6e-4e42-80f2-252530ca9fe7
-- title:
--   Characterization of pure operations
-- statement:
--   Let $H,K$ be complex separable Hilbert spaces, and let $T:B(H)\to B(K)$ be a normal complex-linear CP map satisfying $T(I_H)\le I_K$. Then
--
--   $$\bigl[\exists X:K\to H,\ \|X\|\le1,\ T(A)=X^*AX\ \forall A\bigr]\iff\bigl[\forall S\text{ normal CP},\ S\le T\Rightarrow\exists\lambda\in[0,1],\ S=\lambda T\bigr].$$
--
--   Thus pure operations are exactly those whose dominated operations lie on their scalar ray. The zero operation and $X=0$ are allowed; uniqueness of $\lambda$ is not claimed.
-- source:
--   Radon-Nikodym derivatives of quantum operations, arXiv:math-ph/0303056v3, PDF p. 4, §2.2 and §3.1, unnumbered: characterization of pure operations

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P17

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix Kronecker Topology TensorProduct

open Filter

namespace QAlgorithms.Papers.Independent.Support21.P17

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P50 (NoiseSpace completedTensorMap)

open QAlgorithms.Papers.Independent.Next46.P33 (UltraweakTest)

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

open QAlgorithms.Papers.Independent.Information100.P50 (M Lin coefficientMap)

/-- Sections 2.2 and 3.1, PDF pp.4,8: pure operations are exactly the operations
whose dominated CP maps are scalar multiples. Zero is included and lambda need not be unique. -/
theorem pure_operation_characterization (H K : SeparableHilbertSpace)
    (T : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K) (hT : IsSubunitalNormalCP T) :
    (∃ X : K →L[ℂ] H, ‖X‖ ≤ 1 ∧ ∀ A, T A = compress X A) ↔
    (∀ S : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K, IsNormalCP (StarAlgHom.id ℂ (HilbertEndomorphism H)) S →
      CompletelyDominated S T → ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ S = (c : ℂ) • T) := by sorry

end QAlgorithms.Papers.Independent.Support21.P17

end
