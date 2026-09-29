-- Prove2me | Theorems.Thm_Rep_nonempty_res_tensor_ofMulAction_iso_of_equiv
-- name    : Rep.nonempty_res_tensor_ofMulAction_iso_of_equiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/c81363f3-c1f7-5c20-9465-203a511cb2e7
-- title:
--   Equivariant bijection transports restricted permutation-twisted modules
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, $C \le G$ a subgroup and $M$ an object of $\mathrm{Rep}\,k\,G$ (a $k$-module with a $k$-linear $G$-action), and let $X$, $Y$ be $G$-sets. For a $G$-set $H$, [`Rep.ofMulActionFinsupp k G H`](def/Compat_Mathlib430.html#L100) denotes the permutation module $k[H] = (H \to_0 k)$ of finitely supported $k$-valued functions on $H$, with $g \in G$ acting by push-forward of the support along $h \mapsto g \cdot h$ (`Finsupp.lmapDomain` applied to the translation map). Assume given a bijection $e : X \simeq Y$ which is equivariant for the subgroup $C$ only, i.e. $e(c \cdot x) = c \cdot e(x)$ for all $c \in C$ and $x \in X$ (no compatibility with the action of $G$ outside $C$ is required). Then the type of isomorphisms, in the category of representations of $C$, between the restriction along the inclusion $C \hookrightarrow G$ of $M \otimes k[X]$ and the restriction along the same inclusion of $M \otimes k[Y]$ is nonempty. The assertion is the existence statement `Nonempty (… ≅ …)`, not a designated isomorphism.
--
--   This is the transport of a $C$-equivariant bijection of $G$-sets to an isomorphism of the associated permutation-twisted modules after restriction to $C$; the twisting representation $M$ is carried along unchanged. It supplies the hypothesis of the form "the restricted modules agree" used by [`Rep.eq_zero_of_additive_of_forall_ind_isCyclic_coprime`](thm.html#Rep.eq_zero_of_additive_of_forall_ind_isCyclic_coprime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_nonempty_res_tensor_ofMulAction_iso_of_equiv.lean

import Mathlib
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical

theorem Rep.nonempty_res_tensor_ofMulAction_iso_of_equiv
    {k : Type} [CommRing k] {G : Type} [Group G] (C : Subgroup G) (M : Rep.{0} k G)
    {X Y : Type} [MulAction G X] [MulAction G Y]
    (e : X ≃ Y) (he : ∀ (c : C) (x : X), e ((c : G) • x) = (c : G) • e x) :
    Nonempty (Rep.res C.subtype (M ⊗ Rep.ofMulActionFinsupp k G X) ≅ Rep.res C.subtype (M ⊗ Rep.ofMulActionFinsupp k G Y)) := by sorry
