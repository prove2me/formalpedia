-- Prove2me | Theorems.Thm_Rep_card_smul_eq_zero_of_tateH0
-- name    : Rep.card_smul_eq_zero_of_tateH0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/731bf81d-74ca-52b7-b34f-79cd0f8d3d14
-- title:
--   The order of G annihilates Tate ̂ H⁰
-- statement:
--   Let $k$ be a commutative ring, let $G$ be a group that is finite as a type, and let $A$ be an object of `Rep k G`, that is, a $k$-module with a $k$-linear $G$-action $\rho = A.\rho$. The group `A.tateH0` is by definition the quotient of the submodule $A^G$ of $\rho$-invariants by the range of the $k$-linear map [`Representation.normBar`](def/GroupCohomology_TateCohomology.html#L40), the map induced on coinvariants by the norm $a \mapsto \sum_{g \in G} \rho(g)a$ viewed as a map into the invariants; thus `A.tateH0` $= A^G / N_G(A)$ with $N_G$ the image of the norm. The assertion is that for every element $x$ of this quotient, the scalar multiple $(\mathrm{card}\,G : k) \cdot x$, with the cardinality of $G$ taken as an element of $k$ via the canonical ring map from $\mathbb{N}$, is zero. Equivalently, the $k$-module $\hat H^0(G,A)$ is annihilated by the image of $|G|$ in $k$.
--
--   This is the degree-zero case of the standard fact that Tate cohomology of a finite group is annihilated by the order of the group. It is used by [`Rep.card_smul_eq_zero_of_tateCohomology`](thm.html#Rep.card_smul_eq_zero_of_tateCohomology), which assembles the corresponding annihilation statement across all degrees of Tate cohomology.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_card_smul_eq_zero_of_tateH0.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.card_smul_eq_zero_of_tateH0 {k G : Type*} [CommRing k] [Group G] [Fintype G] (A : Rep k G)
    (x : A.tateH0) : (Fintype.card G : k) • x = 0 := by sorry
