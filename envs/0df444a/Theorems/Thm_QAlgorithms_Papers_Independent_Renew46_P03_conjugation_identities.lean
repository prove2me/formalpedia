-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P03_conjugation_identities
-- name    : QAlgorithms.Papers.Independent.Renew46.P03.conjugation_identities
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:51:52.576362+00:00
-- url     : https://prove2.me/theorems/d39b1f40-48e8-49c0-bad0-33c3db4b71ca
-- title:
--   Corollary 1.4: involution, anti-linear self-adjointness and reversed inner product
-- statement:
--   Let $H$ be a separable complex Hilbert space. Suppose that the bounded conjugate-linear map $K:H\to H$ fixes a complete countable orthonormal basis. Then, for all $x,y\in H$,
--
--   $$K(Kx)=x,\qquad K^*=K,\qquad \langle Kx,Ky\rangle=\langle y,x\rangle.$$
--
--   Here the adjoint of an anti-linear map is characterized by $\langle K^*x,y\rangle=\langle Ky,x\rangle$. These identities establish involution, anti-linear self-adjointness, and antiunitarity without assuming them in the definition of conjugation.
--
--   **Formalization Note** The middle conclusion is stated through that exact defining pairing, rather than the complex-linear adjoint.
-- source:
--   Operator Isomorphisms on Hilbert Space Tensor Products, arXiv:2010.15901v1, PDF p. 3, Corollary 1.4

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P03

universe u v

open QAlgorithms.Papers.Independent.Claimed50.P34 (HilbertTensor)

/-- Corollary 1.4, PDF pp.3–4: involution, anti-linear self-adjointness,
and reversal of the inner product. The middle clause states the adjoint's
exact defining pairing, without applying a complex-linear adjoint to K. -/
theorem conjugation_identities
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (K : H →L⋆[ℂ] H) (hK : IsConjugation K) :
    (∀ x : H, K (K x) = x) ∧ IsAntilinearAdjoint K K ∧
      (∀ x y : H, inner ℂ (K x) (K y) = inner ℂ y x) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P03

end
