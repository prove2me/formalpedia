-- Prove2me | Theorems.Thm_Rep_augShortComplex_shortExact
-- name    : Rep.augShortComplex_shortExact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/a5b66995-d7de-51bc-9ffe-ea5c8f354ab9
-- title:
--   Short exactness of the augmentation sequence of k[G]
-- statement:
--   Let $k$ be a commutative ring and $G$ a group (both types in the same universe). The assertion is that the three-term complex [`Rep.augShortComplex k G`](def/GroupCohomology_SplittingModule.html#L30) of $k$-linear representations of $G$ is short exact in the sense of Mathlib's `ShortComplex.ShortExact`, i.e. its first map is a monomorphism, its second map is an epimorphism, and it is exact at the middle term. The complex in question has middle term the left regular representation [`Rep.leftRegularFinsupp k G`](def/Compat_Mathlib430.html#L103), namely the finitely supported functions $G \to k$ with $G$ acting by left translation, third term the trivial representation on $k$, and second map the augmentation morphism [`Rep.augε k G`](def/GroupCohomology_SplittingModule.html#L18), which sends the indicator function of $1 \in G$ scaled by $r$ to $r$; its first term is [`Rep.augIdeal k G`](def/GroupCohomology_SplittingModule.html#L21), the subrepresentation of [`Rep.leftRegularFinsupp k G`](def/Compat_Mathlib430.html#L103) cut out by the kernel of the underlying $k$-linear map of [`Rep.augε k G`](def/GroupCohomology_SplittingModule.html#L18) (a subrepresentation because the augmentation is $G$-equivariant), and its first map [`Rep.augIdealι k G`](def/GroupCohomology_SplittingModule.html#L27) is the inclusion of that subrepresentation.
--
--   This is the classical augmentation sequence $0 \to I_G \to k[G] \to k \to 0$ of $G$-representations, with the augmentation ideal realised literally as the kernel of the augmentation. It provides the dimension-shifting short exact sequence used in the Tate-cohomology part of the development, and is cited in the proof that the cup product map in [`Rep.IsTateCupProduct.bijective_cup_of_h1_h2`](thm.html#Rep.IsTateCupProduct.bijective_cup_of_h1_h2) is bijective.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_augShortComplex_shortExact.lean

import Mathlib
import Definitions.Def_GroupCohomology_SplittingModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.augShortComplex_shortExact (k G : Type u) [CommRing k] [Group G] :
    (Rep.augShortComplex k G).ShortExact := by sorry
