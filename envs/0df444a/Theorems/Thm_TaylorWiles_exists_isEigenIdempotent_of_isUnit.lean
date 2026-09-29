-- Prove2me | Theorems.Thm_TaylorWiles_exists_isEigenIdempotent_of_isUnit
-- name    : TaylorWiles.exists_isEigenIdempotent_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/ef22b2d0-e96e-5f92-a5ca-a3cb1c055b36
-- title:
--   Unit root separation yields an eigen-idempotent for a 2× 2 matrix
-- statement:
--   Let $A$ be a commutative ring and let $M$ be a $2\times 2$ matrix over $A$, and let $a,b \in A$. Assume that $\operatorname{tr} M = a + b$, that $\det M = ab$, and that the difference $a - b$ is a unit of $A$. The conclusion is that there exists a matrix $e \in M_2(A)$ satisfying the four conditions packaged in the predicate [`TaylorWiles.IsEigenIdempotent M a b e`](def/Deformations_LocalSplitting.html#L13): $e$ is idempotent, $e \cdot e = e$; its trace equals $1$; $M e = a \cdot e$ (scalar multiplication of $e$ by $a$); and $M(1 - e) = b \cdot (1 - e)$. Thus $M$ splits the free module $A^2$ along the idempotent $e$ into a rank-one piece on which $M$ acts by $a$ and a complementary piece on which it acts by $b$. Note that no hypothesis beyond the two coefficient identities and the invertibility of $a-b$ is imposed; in particular $a$ and $b$ need not be distinguished from one another by anything else, and the existence assertion is not accompanied by a uniqueness claim.
--
--   This is the statement that a $2\times 2$ matrix whose characteristic polynomial splits as $(X-a)(X-b)$ with $a-b$ invertible decomposes along an idempotent, the linear-algebra mechanism behind the splitting of local deformations at an auxiliary prime as in Darmon–Diamond–Taylor §2.8. It is used in the construction of a basis in which a matrix is diagonal given information on its characteristic polynomial modulo the maximal ideal, via [`LinearMap.exists_basis_apply_eq_smul_of_charpoly_map_residue_eq`](thm.html#LinearMap.exists_basis_apply_eq_smul_of_charpoly_map_residue_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TaylorWiles_exists_isEigenIdempotent_of_isUnit.lean

import Mathlib
import Definitions.Def_Deformations_LocalSplitting

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open Matrix

theorem TaylorWiles.exists_isEigenIdempotent_of_isUnit {A : Type u} [CommRing A] {M : Matrix (Fin 2) (Fin 2) A} {a b : A}
    (htr : M.trace = a + b) (hdet : M.det = a * b) (hu : IsUnit (a - b)) :
    ∃ e, TaylorWiles.IsEigenIdempotent M a b e := by sorry
