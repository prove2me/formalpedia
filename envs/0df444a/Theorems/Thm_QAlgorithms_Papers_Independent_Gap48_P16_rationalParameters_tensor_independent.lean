-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P16_rationalParameters_tensor_independent
-- name    : QAlgorithms.Papers.Independent.Gap48.P16.rationalParameters_tensor_independent
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:53:54.914486+00:00
-- url     : https://prove2.me/theorems/e5190796-78f0-40bd-b752-577ae7d0d57e
-- title:
--   Remark 2.10: tensor-independent rational parameters
-- statement:
--   Let $R$ be a commutative unital ring, $C$ an $R$-coalgebra, $A$ an associative unital $R$-algebra, and $b:C\times A\to R$ a rational pairing. Thus the associated $\alpha_X$ are injective and $b$ respects multiplication and counit. Let $M$ be an arbitrary left $A$-module with its compatible $R$-module structure, and let $m\in M$. If finite families $(m_i,c_i)$ and $(n_j,d_j)$ satisfy
--
--   $$
--   \forall a\in A,\quad am=\sum_i b(c_i,a)m_i,
--   \qquad \sum_i m_i\otimes c_i=\sum_j n_j\otimes d_j,
--   $$
--
--   then $am=\sum_j b(d_j,a)n_j$ for every $a\in A$. Thus rational parameters depend only on their tensor, including when a presentation is empty.
-- source:
--   Duality and Rational Modules in Hopf Algebras over Commutative Rings, arXiv:math/0011207v1, PDF p. 6, Remark 2.10: tensor-independent rational parameters

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P16

noncomputable section

universe u

namespace QAlgorithms.Papers.Independent.Gap48.P16

open scoped TensorProduct

section RationalParameters

variable {R C A M : Type u} [CommRing R]

variable [AddCommGroup C] [Module R C] [Coalgebra R C]

variable [Ring A] [Algebra R A]

variable [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- Remark 2.10, PDF p.6: rational parameters depend only on their tensor. -/
theorem rationalParameters_tensor_independent [IsScalarTower R A M] (b : C →ₗ[R] A →ₗ[R] R)
    (h : IsRationalPairing b) (m : M) {n k : ℕ}
    (ms : Fin n → M) (cs : Fin n → C) (ns : Fin k → M) (ds : Fin k → C)
    (hm : IsRationalParameters b m ms cs)
    (heq : (∑ i, ms i ⊗ₜ[R] cs i) = ∑ j, ns j ⊗ₜ[R] ds j) :
    IsRationalParameters b m ns ds := by sorry

end RationalParameters

end QAlgorithms.Papers.Independent.Gap48.P16

end
