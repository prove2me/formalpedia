-- Prove2me | Theorems.Thm_Rep_card_smul_eq_zero_of_tateCohomology
-- name    : Rep.card_smul_eq_zero_of_tateCohomology
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/d5053e4a-ce7c-5502-a4e7-3bc31c9886e0
-- title:
--   The order of G annihilates Tate cohomology in all degrees
-- statement:
--   Let $k$ be a commutative ring, $G$ a finite group (in the same universe as $k$), and let $A$ be a $k$-linear representation of $G$. For an integer $q$, the $k$-module $A$`.tateCohomology`$q$ is defined by cases: for $q = n+1 > 0$ it is the group cohomology $H^{n+1}(G,A)$; for $q = 0$ it is the quotient of the $G$-invariants of $A$ by the range of the norm map $\rho$`.normBar` attached to the representation; for $q = -1$ it is the kernel of that same norm map; and for $q = -(n+2)$ it is the group homology $H_{n+1}(G,A)$. The assertion is that for every integer $q$ and every element $x$ of $A$`.tateCohomology`$q$, the scalar $(\lvert G\rvert : k)$, the image of the cardinality of $G$ under the canonical map $\mathbb{N} \to k$, satisfies $(\lvert G\rvert : k) \cdot x = 0$. In other words, Tate cohomology of a finite group is annihilated by the order of the group in every integer degree, for an arbitrary coefficient ring $k$.
--
--   This is the standard fact that $\hat H^q(G,A)$ is $\lvert G\rvert$-torsion for all $q \in \mathbb{Z}$. It underlies the vanishing and finiteness statements for Tate cohomology used later, such as [`Rep.finite_tateCohomology_of_moduleFinite`](thm.html#Rep.finite_tateCohomology_of_moduleFinite), [`Rep.isZero_tateCohomology_of_bijective_card_nsmul`](thm.html#Rep.isZero_tateCohomology_of_bijective_card_nsmul) and [`Rep.isZero_tateCohomology_ihom_of_isPGroup`](thm.html#Rep.isZero_tateCohomology_ihom_of_isPGroup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_card_smul_eq_zero_of_tateCohomology.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.card_smul_eq_zero_of_tateCohomology {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A : Rep.{u} k G) (q : ℤ) (x : A.tateCohomology q) : (Fintype.card G : k) • x = 0 := by sorry
