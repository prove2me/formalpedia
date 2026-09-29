-- Prove2me | Theorems.Thm_Rep_tateDelta_splitting_tateDelta_aug_eq_map_H2pi
-- name    : Rep.tateDelta_splitting_tateDelta_aug_eq_map_H2pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/b3617765-b91a-5a50-8388-0bfd8610be0f
-- title:
--   Fundamental class via two Tate connecting maps
-- statement:
--   Let $k$ be a commutative ring and $G$ a group (both in the same universe), let $C$ be a $k$-linear representation of $G$, let $\varphi$ be an inhomogeneous $2$-cocycle of $G$ with values in $C$, and let $S \le G$ be a subgroup carrying a `Fintype` instance. Two short complexes of $G$-representations are involved: the augmentation complex [`Rep.augShortComplex`](def/GroupCohomology_SplittingModule.html#L30), namely $\mathrm{augIdeal}\,k\,G \to k[G] \to k$ with the inclusion of the kernel of the augmentation followed by the augmentation onto the trivial representation $k$; and the splitting complex [`Rep.splittingShortComplex`](def/GroupCohomology_SplittingModule.html#L140) attached to $\varphi$, namely $C \to \mathrm{splittingModule}\,C\,\varphi \to \mathrm{augIdeal}\,k\,G$. It is assumed that the images of these two short complexes under restriction along the inclusion $S \hookrightarrow G$ are short exact; call these hypotheses `hE` and `hF`. Let $e$ be an invariant vector of the restriction to $S$ of the trivial representation $k$, with $e = 1$ in $k$. Writing $\hat H^0$ for invariants modulo the image of the norm map `normBar` from coinvariants to invariants, the conclusion is that applying the Tate connecting map of `hE` in degree $0$ to the class of $e$ in $\hat H^0$, and then the Tate connecting map of `hF` in degree $1$, yields exactly the image of the class of $\varphi$ in $H^2(G,C)$ under the restriction map to $H^2(S, \mathrm{res}\,C)$ induced by $S \hookrightarrow G$ together with the identity of $\mathrm{res}\,C$.
--
--   This identifies the composite of the two connecting maps attached to the augmentation sequence and to the splitting extension of a $2$-cocycle $\varphi$ with the restriction of the class of $\varphi$; it is the device by which a degree-$2$ class is realised as a double dimension shift in Tate cohomology. It feeds into [`Rep.IsTateCupProduct.bijective_cup_of_h1_h2`](thm.html#Rep.IsTateCupProduct.bijective_cup_of_h1_h2), where cup product with such a class is shown to be bijective.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_tateDelta_splitting_tateDelta_aug_eq_map_H2pi.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_SplittingModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.tateDelta_splitting_tateDelta_aug_eq_map_H2pi {k G : Type u} [CommRing k] [Group G]
    (C : Rep.{u} k G) (φ : groupCohomology.cocycles₂ C) (S : Subgroup G) [Fintype S]
    (hE : ((Rep.augShortComplex k G).map (Rep.resFunctor S.subtype)).ShortExact)
    (hF : ((Rep.splittingShortComplex C φ).map (Rep.resFunctor S.subtype)).ShortExact)
    (e : (Rep.res S.subtype (Rep.trivial k G k)).ρ.invariants) (he : (e : k) = 1) :
    (Rep.tateδ hF 1).hom ((Rep.tateδ hE 0).hom
        (Submodule.Quotient.mk e : (Rep.res S.subtype (Rep.trivial k G k)).tateH0))
      = (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom (groupCohomology.H2π C φ) := by sorry
