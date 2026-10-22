-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P17_canonical_radon_nikodym
-- name    : QAlgorithms.Papers.Independent.Support21.P17.canonical_radon_nikodym
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:39:41.560439+00:00
-- url     : https://prove2.me/theorems/69976571-46aa-4e9a-816e-32690570c122
-- title:
--   Canonical tensor Radon–Nikodym form
-- statement:
--   Let $H,K,E$ be complex separable Hilbert spaces, allowing zero spaces. Let $S,T:B(H)\to B(K)$ be normal complex-linear CP maps, and fix a canonical minimal dilation $T(A)=V^*(A\otimes I_E)V$. Then
--
--   $$S\le T\iff\exists F\in B(E),\quad 0\le F\le I_E,\qquad S(A)=V^*(A\otimes F)V\quad(A\in B(H)).$$
--
--   If $H$ is nonzero, the representing $F$ is unique even among all bounded environment operators satisfying this compression identity. This conditional uniqueness follows from Theorem 3.1 and faithfulness of $F\mapsto I_H\otimes F$. When $H=0$, the printed existence equivalence still holds; uniqueness of $F$ is not asserted.
-- source:
--   Radon-Nikodym derivatives of quantum operations, arXiv:math-ph/0303056v3, PDF p. 8, Corollary 3.2: canonical tensor form

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

/-- Corollary 3.2, PDF p.8: the canonical tensor RN equivalence includes zero input
spaces. Strong coefficient uniqueness inherited from Theorem 3.1 is asserted only
when H is nonzero, so F ↦ I tensor F is faithful. -/
theorem canonical_radon_nikodym (H K E : SeparableHilbertSpace)
    (T : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K) (V : K →L[ℂ] NoiseSpace H E)
    (hT : IsNormalCP (StarAlgHom.id ℂ (HilbertEndomorphism H)) T) (hV : IsCanonical T V)
    (S : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K) (hS : IsNormalCP (StarAlgHom.id ℂ (HilbertEndomorphism H)) S) :
    CompletelyDominated S T ↔ ∃ F : HilbertEndomorphism E, PositiveContraction F ∧
      (∀ A, S A = compress V (completedTensorMap A F)) ∧
      (Nontrivial H → ∀ Y : HilbertEndomorphism E,
        (∀ A, S A = compress V (completedTensorMap A Y)) → Y = F) := by sorry

end QAlgorithms.Papers.Independent.Support21.P17

end
