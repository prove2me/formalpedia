-- Prove2me | Theorems.Thm_SymplecticMatrix_span_standardBasisSet_eq_sp
-- name    : SymplecticMatrix.span_standardBasisSet_eq_sp
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T15:44:12.929373+00:00
-- url     : https://prove2.me/theorems/34045326-94f3-4b50-a542-683e5abe57b3
-- title:
--   The standard families span $\mathfrak{sp}_{2l}(R)$
-- statement:
--   Let $R$ be a commutative ring and let $\mathfrak{sp}_{2l}(R)$ be the symplectic Lie algebra, realized as the matrices that are skew-adjoint for the canonical alternating form
--
--   $$
--   J=\begin{pmatrix}0&-I\\ I&0\end{pmatrix},
--   \qquad\text{that is}\qquad A^{\mathsf T}J=-JA .
--   $$
--
--   This theorem asserts that the three standard families span the symplectic Lie algebra as an $R$-module:
--
--   $$
--   \operatorname{span}_R\bigl(\{X_{i,j}\}\cup\{S_{i,j}\}\cup\{T_{i,j}\}\bigr)=\mathfrak{sp}_{2l}(R).
--   $$
--
--   Combined with the block criterion, the content is that an arbitrary $l\times l$ matrix is a linear combination of the matrix units $E_{i,j}$, and an arbitrary symmetric matrix is a linear combination of the $\Sigma_{i,j}$ with $i\le j$. The diagonal convention $\Sigma_{i,i}=E_{i,i}$, rather than $2E_{i,i}$, is what keeps the second statement true over a commutative ring in which $2$ is not invertible.
--
--   The family is in fact a basis, of cardinality $l^2+l(l+1)=l(2l+1)$, the familiar dimension of the symplectic Lie algebra of rank $l$; only the spanning half is asserted here, since that is what the generation statement consumes.
-- source:
--   Standard structure theory of the classical Lie algebra of type C_l; see e.g. J. E. Humphreys, Introduction to Lie Algebras and Representation Theory, Springer GTM 9, Section 1.2 (type C_l). Mathlib provides only the definition LieAlgebra.Symplectic.sp in Mathlib/Algebra/Lie/Classical.lean, with no membership criterion, block description, spanning family or generating set.

import Definitions.Def_symplectic_block_generators

namespace SymplecticMatrix

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {l : ℕ} {R : Type*} [CommRing R]

theorem span_standardBasisSet_eq_sp (l : ℕ) (R : Type*) [CommRing R] :
    Submodule.span R (standardBasisSet l R)
      = (LieAlgebra.Symplectic.sp (Fin l) R).toSubmodule := by sorry

end SymplecticMatrix
