-- Prove2me | Theorems.Thm_Rep_tateMap_id
-- name    : Rep.tateMap_id
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/abadb31e-df49-5b5a-9a94-12654e3f6186
-- title:
--   Tate cohomology: the identity map induces the identity
-- statement:
--   Let $k$ be a commutative ring and $G$ a finite group, let $A$ be an object of $\mathrm{Rep}\,k\,G$ (a $k$-linear representation $A$ with action $A.\rho$), and let $n$ be an integer. The statement asserts that the morphism [`Rep.tateMap (𝟙 A) n`](def/GroupCohomology_TateShiftMaps.html#L17) of $k$-modules induced by the identity morphism of $A$ on the $n$-th Tate cohomology object `A.tateCohomology n` is the identity morphism of that object. Here `tateCohomology` is defined by cases on $n$: for $n \ge 1$ it is the group cohomology $H^n(G,A)$, for $n = 0$ it is the module of invariants $A.\rho.\mathrm{invariants}$ modulo the range of the map `normBar` attached to $A.\rho$ (which goes from the coinvariants to the invariants), for $n = -1$ it is the kernel of that same map `normBar` inside the coinvariants, and for $n \le -2$ it is the group homology $H_{-n-1}(G,A)$; correspondingly `tateMap` is given by `groupCohomology.map` along the identity of $G$ in positive degrees, by the map induced on invariants modulo the range of `normBar` in degree $0$, by the map induced on the kernel of `normBar` in degree $-1$, and by `groupHomology.map` along the identity of $G$ in degrees $\le -2$.
--
--   This is one half of the functoriality of Tate cohomology in the representation variable, the companion of compatibility with composition. It is used in the treatment of the Tate cup product and of the Tate–Nakayama pairing, for instance by [`Rep.IsTateCupProduct.bijective_cup_of_h1_h2`](thm.html#Rep.IsTateCupProduct.bijective_cup_of_h1_h2) and [`Rep.IsTateCupProduct.tateNakayamaPairing_right_eq_zero`](thm.html#Rep.IsTateCupProduct.tateNakayamaPairing_right_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_tateMap_id.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.tateMap_id {k G : Type u} [CommRing k] [Group G] [Fintype G] (A : Rep.{u} k G) (n : ℤ) :
    Rep.tateMap (𝟙 A) n = 𝟙 (A.tateCohomology n) := by sorry
