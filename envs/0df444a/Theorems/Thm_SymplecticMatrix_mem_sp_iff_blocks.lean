-- Prove2me | Theorems.Thm_SymplecticMatrix_mem_sp_iff_blocks
-- name    : SymplecticMatrix.mem_sp_iff_blocks
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T15:43:42.108557+00:00
-- url     : https://prove2.me/theorems/ae635b82-a32c-4e2b-95a2-cd4f576245e2
-- title:
--   Block criterion for membership in $\mathfrak{sp}_{2l}(R)$
-- statement:
--   Let $R$ be a commutative ring and let $\mathfrak{sp}_{2l}(R)$ be the symplectic Lie algebra, realized as the matrices that are skew-adjoint for the canonical alternating form
--
--   $$
--   J=\begin{pmatrix}0&-I\\ I&0\end{pmatrix},
--   \qquad\text{that is}\qquad A^{\mathsf T}J=-JA .
--   $$
--
--   This theorem is the block criterion for membership. Writing a $2l\times2l$ matrix in $l\times l$ blocks,
--
--   $$
--   \begin{pmatrix} a & b\\ c & d\end{pmatrix}\in\mathfrak{sp}_{2l}(R)
--   \iff
--   d=-a^{\mathsf T},\quad b^{\mathsf T}=b,\quad c^{\mathsf T}=c .
--   $$
--
--   So an element of the symplectic Lie algebra is exactly a choice of an arbitrary $l\times l$ matrix $a$, which is placed in the upper-left block with its negative transpose in the lower-right, together with two symmetric matrices in the off-diagonal blocks. The upper-left block carries a copy of $\mathfrak{gl}_l$, and the two off-diagonal blocks carry the abelian nilradical of the Siegel parabolic subalgebra and its opposite.
--
--   Only three of the four block conditions produced by expanding $A^{\mathsf T}J=-JA$ are recorded, because the fourth, $d^{\mathsf T}=-a$, is a consequence of $d=-a^{\mathsf T}$.
--
--   This criterion is what makes the symplectic Lie algebra usable in practice: every concrete verification that a matrix is symplectic reduces to reading off its blocks.
-- source:
--   Standard structure theory of the classical Lie algebra of type C_l; see e.g. J. E. Humphreys, Introduction to Lie Algebras and Representation Theory, Springer GTM 9, Section 1.2 (type C_l). Mathlib provides only the definition LieAlgebra.Symplectic.sp in Mathlib/Algebra/Lie/Classical.lean, with no membership criterion, block description, spanning family or generating set.

import Definitions.Def_symplectic_block_generators

namespace SymplecticMatrix

open Matrix

variable {l : ℕ} {R : Type*} [CommRing R]

theorem mem_sp_iff_blocks (a b c d : Matrix (Fin l) (Fin l) R) :
    Matrix.fromBlocks a b c d ∈ LieAlgebra.Symplectic.sp (Fin l) R ↔
      d = -a.transpose ∧ b.transpose = b ∧ c.transpose = c := by sorry

end SymplecticMatrix
