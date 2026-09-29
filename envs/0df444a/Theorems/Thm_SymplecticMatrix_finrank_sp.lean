-- Prove2me | Theorems.Thm_SymplecticMatrix_finrank_sp
-- name    : SymplecticMatrix.finrank_sp
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T17:10:35.740276+00:00
-- url     : https://prove2.me/theorems/c6511f10-beda-4af5-8c04-5f4bc3939245
-- title:
--   $\dim \mathfrak{sp}_{2l}(R) = l(2l+1)$
-- statement:
--   Let $R$ be a field. The symplectic Lie algebra of rank $l$ has dimension
--
--   $$
--   \dim_R \mathfrak{sp}_{2l}(R) = l\,(2l+1).
--   $$
--
--   The count is visible from the block description. An element of $\mathfrak{sp}_{2l}(R)$ is an arbitrary $l\times l$ matrix $a$ placed in the upper-left block, with $-a^{\mathsf T}$ opposite it, together with two symmetric $l\times l$ matrices in the off-diagonal blocks. That is
--
--   $$
--   l^2 \;+\; 2\cdot\frac{l(l+1)}{2} \;=\; l^2 + l(l+1) \;=\; l(2l+1)
--   $$
--
--   free parameters, matching the classical dimension of the Lie algebra of type $C_l$.
--
--   Formally the statement follows from the standard family being a basis: it is linearly independent and spans, and its index set is the disjoint union of $\{1,\dots,l\}^2$ with two copies of the set of pairs $i\le j$, whose cardinality is $\binom{l+1}{2}$.
--
--   Mathlib records only the definition of $\mathfrak{sp}_{2l}$ as a set of skew-adjoint matrices, so neither its basis nor its dimension was previously available.
-- source:
--   Standard structure theory of the classical Lie algebra of type C_l; see e.g. J. E. Humphreys, Introduction to Lie Algebras and Representation Theory, Springer GTM 9, Section 1.2, where the dimension l(2l+1) of sp_{2l} is computed from exactly this block description. Mathlib provides only the definition LieAlgebra.Symplectic.sp in Mathlib/Algebra/Lie/Classical.lean, with no basis or dimension.

import Definitions.Def_symplectic_block_generators

namespace SymplecticMatrix

theorem finrank_sp (l : ℕ) (R : Type*) [Field R] :
    Module.finrank R (LieAlgebra.Symplectic.sp (Fin l) R) = l * (2 * l + 1) := by sorry

end SymplecticMatrix
