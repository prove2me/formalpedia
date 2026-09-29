-- Prove2me | Theorems.Thm_Rep_finite_tateCohomology_of_moduleFinite
-- name    : Rep.finite_tateCohomology_of_moduleFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/f4719cde-89ab-5591-9c6e-bf2bfed041ca
-- title:
--   Finiteness of Tate cohomology for finitely generated ℤ[G]-coefficients
-- statement:
--   Let $G$ be a finite group (a group with a `Fintype` structure, living in the smallest universe), and let $L$ be an object of `Rep ℤ G`, i.e. an abelian group with an action of $G$ by automorphisms, whose underlying $\mathbb Z$-module is finitely generated. Then for every integer $n$ the $\mathbb Z$-module `L.tateCohomology n` is finite, i.e. has finitely many elements. Here `tateCohomology` is defined by cases on the integer: for $n = m+1 > 0$ it is the group cohomology $H^{m+1}(G, L)$; for $n = 0$ it is the quotient $L^G / \operatorname{range}(\overline{N})$ of the invariants by the image of the map $\overline{N}$ induced by the norm $\sum_{g \in G} \rho(g)$; for $n = -1$ it is the kernel of $\overline{N}$ (a submodule of the coinvariants); and for $n = -m-2 \le -2$ it is the group homology $H_{m+1}(G, L)$.
--
--   This is the standard finiteness statement for the Tate cohomology of a finite group acting on a finitely generated abelian group, in all integer degrees at once. It is used in the verification of Tate duality for cup products, being cited by [`Rep.IsTateCupProduct.bijective_cupEv_dual_left`](thm.html#Rep.IsTateCupProduct.bijective_cupEv_dual_left) and [`Rep.IsTateCupProduct.exists_cupEv_dual_right_eq`](thm.html#Rep.IsTateCupProduct.exists_cupEv_dual_right_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_finite_tateCohomology_of_moduleFinite.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Rep

theorem Rep.finite_tateCohomology_of_moduleFinite {G : Type} [Group G] [Fintype G]
    (L : Rep ℤ G) [Module.Finite ℤ L] (n : ℤ) :
    Finite (L.tateCohomology n) := by sorry
