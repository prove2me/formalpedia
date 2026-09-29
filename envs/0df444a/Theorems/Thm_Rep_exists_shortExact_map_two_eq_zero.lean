-- Prove2me | Theorems.Thm_Rep_exists_shortExact_map_two_eq_zero
-- name    : Rep.exists_shortExact_map_two_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/95dddcb6-3fa5-5964-ad5d-851dee0ff90e
-- title:
--   Splitting module: every H² class dies over the augmentation module
-- statement:
--   Let $k$ be a commutative ring and $G$ a group (both in the same universe), let $C$ be a $k$-linear representation of $G$, and let $u$ be a class in $H^2(G,C)$, i.e. an element of `groupCohomology C 2`. Write $I$ for `(Rep.trivial k G k).dimShiftDownObj`: the subrepresentation of `(Rep.trivial k G k).indBot`, the module induced along the inclusion $\bot \le G$ from the restriction of the trivial representation $k$ to the trivial subgroup, cut out by the kernel of the underlying linear map of the canonical morphism `indBotπ (Rep.trivial k G k)`, this kernel being $G$-stable. The assertion is that there exist a representation $B$ of $G$ over $k$, morphisms $i : C \to B$ and $p : B \to I$ of representations, and a proof $w$ that $i$ followed by $p$ is the zero morphism, such that the short complex $C \xrightarrow{i} B \xrightarrow{p} I$ determined by $w$ is short exact ($i$ a monomorphism, $p$ an epimorphism, exact in the middle) and such that the map on second group cohomology induced by $i$, namely the value of `(groupCohomology.functor k G 2).map i` on underlying modules, sends $u$ to $0$.
--
--   This is Tate's splitting module construction in dimension-shifting form: any prescribed class in $H^2(G,C)$ becomes trivial after pushing forward along a suitable extension of the augmentation module $I$ by $C$. It is used in the comparison of Tate cohomology of the trivial module with the given representation, via [`Rep.nonempty_tateCohomology_trivial_iso_of_h1_h2`](thm.html#Rep.nonempty_tateCohomology_trivial_iso_of_h1_h2).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exists_shortExact_map_two_eq_zero.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.exists_shortExact_map_two_eq_zero {k G : Type u} [CommRing k] [Group G] (C : Rep.{u} k G)
    (u : groupCohomology C 2) :
    ∃ (B : Rep.{u} k G) (i : C ⟶ B) (p : B ⟶ (Rep.trivial k G k).dimShiftDownObj) (w : i ≫ p = 0),
      (CategoryTheory.ShortComplex.mk i p w).ShortExact ∧ ((groupCohomology.functor k G 2).map i).hom u = 0 := by sorry
