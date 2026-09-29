-- Prove2me | Theorems.Thm_Rep_isZero_tateCohomology_indBot_tensor
-- name    : Rep.isZero_tateCohomology_indBot_tensor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/a2df7318-a833-5b84-8179-b70c14ea4e73
-- title:
--   Vanishing of Tate cohomology of Ind₁^GRes₁ A ⊗ B
-- statement:
--   Let $k$ be a commutative ring and $G$ a finite group (both in the same universe), and let $A$ and $B$ be $k$-linear representations of $G$. Write $A_* = \mathrm{Ind}\,\mathrm{Res}\,A$ for [`Rep.indBot`](def/GroupCohomology_TateDimensionShift.html#L18), the representation obtained by restricting $A$ along the inclusion of the trivial subgroup $\bot \le G$ and then inducing along the same inclusion, and form the tensor product $A_* \otimes B$ in the monoidal category $\mathrm{Rep}_k(G)$, that is, the tensor product over $k$ with the diagonal action. Then for every integer $q$ the Tate cohomology module $\hat H^q(G, A_* \otimes B)$ is a zero object of $\mathrm{Mod}_k$. Here Tate cohomology is the object defined by cases: for $q = n+1 \ge 1$ it is the group cohomology $H^{n+1}(G, -)$, for $q = 0$ it is the invariants modulo the range of `normBar` of the representation, for $q = -1$ it is the kernel of `normBar`, and for $q = -(n+1) \le -2$ it is the group homology $H_{n+1}(G, -)$.
--
--   This is the vanishing statement underlying dimension shifting with coefficients: tensoring a representation induced from the trivial subgroup with an arbitrary $B$ again has trivial Tate cohomology, so that short exact sequences built from $A_*\otimes B$ produce isomorphisms between Tate cohomology groups in adjacent degrees. It is used in the construction and in the verification of the associativity, commutativity and compatibility properties of the Tate cup product.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_isZero_tateCohomology_indBot_tensor.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory

theorem Rep.isZero_tateCohomology_indBot_tensor {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A B : Rep.{u} k G) (q : ℤ) :
    CategoryTheory.Limits.IsZero ((A.indBot ⊗ B).tateCohomology q) := by sorry
