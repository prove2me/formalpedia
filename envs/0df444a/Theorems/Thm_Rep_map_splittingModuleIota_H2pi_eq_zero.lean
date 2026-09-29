-- Prove2me | Theorems.Thm_Rep_map_splittingModuleIota_H2pi_eq_zero
-- name    : Rep.map_splittingModuleIota_H2pi_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/73502aeb-9ce4-59f2-b5a6-0304b61159e7
-- title:
--   Image of [φ] in the splitting module vanishes
-- statement:
--   Let $k$ be a commutative ring and $G$ a group (both in the same universe), let $C$ be an object of `Rep k G`, i.e. a $k$-linear representation of $G$, and let $\varphi$ be an element of `groupCohomology.cocycles₂ C`, a $2$-cocycle of $G$ with values in $C$ in the inhomogeneous normalisation used by Mathlib. Associated with these data is the splitting module [`Rep.splittingModule C φ`](def/GroupCohomology_SplittingModule.html#L124), the representation whose underlying $k$-module is $C \times I$, where $I =$ [`Rep.augIdeal k G`](def/GroupCohomology_SplittingModule.html#L21) is the kernel of the augmentation [`Rep.augε k G`](def/GroupCohomology_SplittingModule.html#L18) on the group ring (elements being finitely supported functions $G \to k$), and on which $\sigma \in G$ acts by $(c,x) \mapsto (\rho_C(\sigma)c + (\mathrm{cocycleTwist}\,C\,\varphi\,\sigma)(x),\ \rho_I(\sigma)x)$, together with the morphism [`Rep.splittingModuleι C φ`](def/GroupCohomology_SplittingModule.html#L129) from $C$ to it. The assertion is that the $k$-linear map underlying the image of this morphism under the functor `groupCohomology.functor k G 2` sends the class `groupCohomology.H2π C φ` of $\varphi$ in $H^2(G,C)$ to $0$ in $H^2(G,$ [`Rep.splittingModule C φ`](def/GroupCohomology_SplittingModule.html#L124) $)$.
--
--   This is the explicit form of the standard fact that a $2$-cocycle class becomes a coboundary in the extension of $C$ by the augmentation ideal that it determines; the vanishing is witnessed by a named $1$-cochain. It is used in [`Rep.isZero_tateCohomology_res_splittingModule`](thm.html#Rep.isZero_tateCohomology_res_splittingModule).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_map_splittingModuleIota_H2pi_eq_zero.lean

import Mathlib
import Definitions.Def_GroupCohomology_SplittingModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.map_splittingModuleIota_H2pi_eq_zero {k G : Type u} [CommRing k] [Group G]
    (C : Rep.{u} k G) (φ : groupCohomology.cocycles₂ C) :
    ((groupCohomology.functor k G 2).map (Rep.splittingModuleι C φ)).hom (groupCohomology.H2π C φ) = 0 := by sorry
