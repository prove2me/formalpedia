-- Prove2me | Theorems.Thm_Rep_splittingShortComplex_shortExact
-- name    : Rep.splittingShortComplex_shortExact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/decd129f-5fe8-54e1-baf2-264d0d18a555
-- title:
--   Short exactness of the splitting sequence of a 2-cocycle
-- statement:
--   Let $k$ be a commutative ring and $G$ a group (both in the same universe), let $C$ be an object of $\mathrm{Rep}\,k\,G$, i.e. a $k$-linear representation of $G$, and let $\varphi$ be an element of `groupCohomology.cocycles₂ C`, the $k$-module of inhomogeneous $2$-cocycles of $G$ with values in $C$. The assertion is that the short complex [`Rep.splittingShortComplex C φ`](def/GroupCohomology_SplittingModule.html#L140) in $\mathrm{Rep}\,k\,G$ is short exact. That short complex has $X_1 = C$, $X_2$ the splitting module `Rep.of (splittingRep C φ)` attached to $C$ and $\varphi$, and $X_3$ the augmentation ideal `augIdeal k G`, namely the subrepresentation of the left regular representation of $G$ on finitely supported functions $G \to k$ cut out by the kernel of the augmentation morphism `augε k G`; its maps are $f =$ `splittingModuleι C φ` and $g =$ `splittingModuleπ C φ`, whose composite is zero. Short exactness means: the complex is exact at the middle term, $f$ is a monomorphism and $g$ is an epimorphism. Concretely, the underlying $k$-module of the splitting module is the product of $C$ with the augmentation ideal, with $f$ the inclusion of the first factor and $g$ the projection to the second.
--
--   This is the short exactness of the classical splitting sequence $0 \to C \to C(\varphi) \to I_G \to 0$ associated with a $2$-cocycle $\varphi$, the representation $C(\varphi)$ being the extension of the augmentation ideal by $C$ determined by $\varphi$. It serves the computation of the Tate cohomology of the splitting module, being cited by [`Rep.isZero_tateCohomology_res_splittingModule`](thm.html#Rep.isZero_tateCohomology_res_splittingModule) and by [`Rep.IsTateCupProduct.bijective_cup_of_h1_h2`](thm.html#Rep.IsTateCupProduct.bijective_cup_of_h1_h2).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_splittingShortComplex_shortExact.lean

import Mathlib
import Definitions.Def_GroupCohomology_SplittingModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.splittingShortComplex_shortExact {k G : Type u} [CommRing k] [Group G]
    (C : Rep.{u} k G) (φ : groupCohomology.cocycles₂ C) :
    (Rep.splittingShortComplex C φ).ShortExact := by sorry
