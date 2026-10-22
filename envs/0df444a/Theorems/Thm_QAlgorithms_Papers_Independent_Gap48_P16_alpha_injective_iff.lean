-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P16_alpha_injective_iff
-- name    : QAlgorithms.Papers.Independent.Gap48.P16.alpha_injective_iff
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:51:22.264211+00:00
-- url     : https://prove2.me/theorems/62c9a6ce-0c5e-4c49-82a1-253778e30b54
-- title:
--   Proposition 2.1
-- statement:
--   Let $R$ be a commutative unital ring, let $P,A,M$ be arbitrary $R$-modules, and let $b:P\times A\to R$ be bilinear. Define $\alpha_M:M\otimes_R P\to\operatorname{Hom}_R(A,M)$ by $\alpha_M(m\otimes p)(a)=b(p,a)m$. Then
--
--   $$
--   \alpha_M\text{ is injective}\quad\Longleftrightarrow\quad
--   \forall n\ge0,\ m_1,\ldots,m_n\in M,\ p_1,\ldots,p_n\in P,\quad
--   \left(\sum_i m_i\otimes p_i=0\ \Longleftrightarrow\ \forall a\in A,\ \sum_i b(p_i,a)m_i=0\right).
--   $$
--
--   This identifies the tensor kernel using all finite presentations, including the empty presentation.
-- source:
--   Duality and Rational Modules in Hopf Algebras over Commutative Rings, arXiv:math/0011207v1, PDF p. 4, Proposition 2.1

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P16

noncomputable section

universe u

namespace QAlgorithms.Papers.Independent.Gap48.P16

open scoped TensorProduct

section Pairings

variable {R A P Q B M : Type u} [CommRing R]

variable [AddCommGroup A] [Module R A] [AddCommGroup P] [Module R P]

variable [AddCommGroup Q] [Module R Q] [AddCommGroup B] [Module R B]

variable [AddCommGroup M] [Module R M]

/-- Proposition 2.1, PDF pp.3-4: the finite-presentation kernel criterion. -/
theorem alpha_injective_iff (b : P →ₗ[R] A →ₗ[R] R) :
    Function.Injective (pairingAlpha b M) ↔
      ∀ (n : ℕ) (m : Fin n → M) (p : Fin n → P),
        ((∑ i, m i ⊗ₜ[R] p i) = 0 ↔ ∀ a : A, (∑ i, b (p i) a • m i) = 0) := by sorry

end Pairings

end QAlgorithms.Papers.Independent.Gap48.P16

end
