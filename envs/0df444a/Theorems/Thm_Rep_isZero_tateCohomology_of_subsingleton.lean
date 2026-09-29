-- Prove2me | Theorems.Thm_Rep_isZero_tateCohomology_of_subsingleton
-- name    : Rep.isZero_tateCohomology_of_subsingleton
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/3043c773-2c45-5bcb-b52d-6fdcdc580e4a
-- title:
--   Tate cohomology of the trivial group vanishes
-- statement:
--   Let $k$ be a commutative ring and let $G$ be a group that is finite and has at most one element, i.e. is trivial (both types in the same universe). For every $k$-linear representation $A$ of $G$ and every integer $q$, the object $A.tateCohomology q$ of the category of $k$-modules is a zero object in the sense of `CategoryTheory.Limits.IsZero`. Here `tateCohomology` is defined by cases on $q$: for $q = n+1 > 0$ it is the group cohomology $H^{n+1}(G, A)$; for $q = 0$ it is the $k$-module $A^G / \operatorname{im}(\bar N)$, the $G$-invariants of $A$ modulo the range of the map $\bar N$ induced by the norm $\sum_{g \in G} \rho(g)$ on the coinvariants of $A$ with values in the invariants; for $q = -1$ it is the kernel of that same map $\bar N$ on the coinvariants; and for $q = -(n+2)$ it is the group homology $H_{n+1}(G, A)$. Thus all four branches are asserted to be zero.
--
--   This is the vanishing of Tate cohomology $\widehat H^q(G,A)$ in all degrees for the trivial group, the base case for inductions on the order of $G$. It is used by [`Rep.isZero_tateCohomology_of_isPGroup_of_forall`](thm.html#Rep.isZero_tateCohomology_of_isPGroup_of_forall), the $p$-group step towards the Nakayama–Tate criterion for cohomological triviality.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_isZero_tateCohomology_of_subsingleton.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.isZero_tateCohomology_of_subsingleton {k G : Type u} [CommRing k] [Group G] [Fintype G] [Subsingleton G]
    (A : Rep.{u} k G) (q : ℤ) : CategoryTheory.Limits.IsZero (A.tateCohomology q) := by sorry
