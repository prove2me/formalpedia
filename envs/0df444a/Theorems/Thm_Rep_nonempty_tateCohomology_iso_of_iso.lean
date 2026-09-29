-- Prove2me | Theorems.Thm_Rep_nonempty_tateCohomology_iso_of_iso
-- name    : Rep.nonempty_tateCohomology_iso_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/914a0127-b09b-5fef-80a6-4d50e1d97433
-- title:
--   Tate cohomology is invariant under isomorphism of representations
-- statement:
--   Let $k$ be a commutative ring, $G$ a group with finitely many elements, and let $A$ and $B$ be $k$-linear representations of $G$ (objects of `Rep k G`, with $k$, $G$ and the underlying modules in one universe). Suppose $e : A \cong B$ is an isomorphism in `Rep k G`, and let $q$ be an integer. The assertion is that the type of isomorphisms $A.\mathrm{tateCohomology}\,q \cong B.\mathrm{tateCohomology}\,q$ in `ModuleCat k` is nonempty, i.e. such an isomorphism exists without one being named. Here `tateCohomology` is the piecewise integer-graded $k$-module attached to a representation: in degree $n+1 \ge 1$ it is the group cohomology $H^{n+1}(G,A)$; in degree $0$ it is the quotient of the invariants $A^G$ by the range of the map `A.ρ.normBar`; in degree $-1$ it is the kernel of `A.ρ.normBar`; and in degree $-(n+2) \le -2$ it is the group homology $H_{n+1}(G,A)$. Thus for every integer $q$ an isomorphism of $k$-modules between the $q$-th Tate groups of $A$ and of $B$ exists.
--
--   This records functoriality of the piecewise-defined Tate cohomology of a finite group in the coefficient representation, in the minimal form of invariance of each graded piece under isomorphism. It is used to transport vanishing, dimension-shifting and cup-product statements along isomorphisms of representations; within the development it is cited by results on Tate cup products ([`Rep.IsTateCupProduct.bijective_cup_of_h1_h2`](thm.html#Rep.IsTateCupProduct.bijective_cup_of_h1_h2), [`Rep.IsTateCupProduct.cup_assoc`](thm.html#Rep.IsTateCupProduct.cup_assoc)) and by [`Rep.exists_shortExact_free_of_forall_isZero`](thm.html#Rep.exists_shortExact_free_of_forall_isZero), among others.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_nonempty_tateCohomology_iso_of_iso.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.nonempty_tateCohomology_iso_of_iso {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {A B : Rep.{u} k G} (e : A ≅ B) (q : ℤ) : Nonempty (A.tateCohomology q ≅ B.tateCohomology q) := by sorry
