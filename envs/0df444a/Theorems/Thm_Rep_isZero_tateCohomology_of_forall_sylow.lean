-- Prove2me | Theorems.Thm_Rep_isZero_tateCohomology_of_forall_sylow
-- name    : Rep.isZero_tateCohomology_of_forall_sylow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/899f7e39-f7ac-58ea-bd06-a3373bbfda1d
-- title:
--   Sylow reduction for vanishing of Tate cohomology
-- statement:
--   Let $k$ be a commutative ring, $G$ a finite group, $A$ a $k$-linear representation of $G$ (an object of `Rep k G`), and $q$ an integer. Suppose that for every prime $p$ and every Sylow $p$-subgroup $P$ of $G$ the $k$-module $(\mathrm{Res}^G_P A)^{\widehat{}\,q}$, the $q$-th Tate cohomology of the restriction of $A$ along the inclusion $P \hookrightarrow G$, is a zero object of `ModuleCat k`. Then the $q$-th Tate cohomology of $A$ itself is a zero object. Here the Tate cohomology of a representation in degree $q$ is defined by cases: for $q = n+1 > 0$ it is the group cohomology $H^{n+1}(G, A)$; for $q = 0$ it is the quotient of the $G$-invariants of $A$ by the range of the map `normBar` attached to the representation; for $q = -1$ it is the kernel of that same map; and for $q = -(n+2) < -1$ it is the group homology $H_{n+1}(G, A)$. No hypothesis is imposed on $k$ beyond commutativity, and none on $A$ beyond being a $k$-linear $G$-representation; the hypothesis and the conclusion concern one and the same degree $q$.
--
--   This is the classical Sylow reduction for the vanishing of Tate cohomology of a finite group: a class vanishes over $G$ as soon as it vanishes over every Sylow subgroup. It feeds the criteria [`Rep.exists_retract_free_of_forall_isZero`](thm.html#Rep.exists_retract_free_of_forall_isZero) and [`Rep.isZero_tateCohomology_res_of_forall_isPGroup`](thm.html#Rep.isZero_tateCohomology_res_of_forall_isPGroup) used in the cohomological-triviality machinery.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_isZero_tateCohomology_of_forall_sylow.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.isZero_tateCohomology_of_forall_sylow {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A : Rep.{u} k G) (q : ℤ)
    (h : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) [Fintype (P : Subgroup G)],
      CategoryTheory.Limits.IsZero ((Rep.res (P : Subgroup G).subtype A).tateCohomology q)) :
    CategoryTheory.Limits.IsZero (A.tateCohomology q) := by sorry
