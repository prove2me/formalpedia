-- Prove2me | Theorems.Thm_Rep_nonempty_ind_res_iso_tensor_ofMulAction_quotient
-- name    : Rep.nonempty_ind_res_iso_tensor_ofMulAction_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/95715cdf-f2a1-582b-b7d2-d178d87a4108
-- title:
--   Projection formula: Ind_D^GRes_D^G M ≅ M ⊗ k[G/D]
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, $D \le G$ a subgroup, and let $M$ be an object of `Rep k G`, that is a $k$-module with a $k$-linear $G$-action (taken in universe $0$). The assertion is that the type of isomorphisms in `Rep k G` between two objects is nonempty. The first object is `Rep.ind D.subtype (Rep.res D.subtype M)`: the representation of $G$ induced along the inclusion homomorphism $D \hookrightarrow G$ from the restriction of $M$ to $D$. The second is the monoidal product $M \otimes$ [`Rep.ofMulActionFinsupp k G (G ⧸ D)`](def/Compat_Mathlib430.html#L100) in `Rep k G`, where [`Rep.ofMulActionFinsupp k G (G ⧸ D)`](def/Compat_Mathlib430.html#L100) is the representation of $G$ on the $k$-module $(G/D) \to_{0} k$ of finitely supported functions on the left coset space $G/D$, with $g$ acting by relabelling the support along $q \mapsto g \cdot q$ (`Finsupp.lmapDomain` applied to $(g \bullet \cdot)$); thus the second object is $M \otimes_k k[G/D]$ with the diagonal action. Only the existence of such an isomorphism is asserted, in the `Nonempty` form, not a designated one.
--
--   This is the projection formula $\operatorname{Ind}_D^G(\operatorname{Res}_D^G M \otimes N) \cong M \otimes \operatorname{Ind}_D^G N$ specialised to the trivial representation $N = k$, for which $\operatorname{Ind}_D^G k$ is the permutation module $k[G/D]$. It is used in [`Rep.eq_zero_of_additive_of_forall_ind_isCyclic_coprime`](thm.html#Rep.eq_zero_of_additive_of_forall_ind_isCyclic_coprime), where twists $M \otimes k[G/D]$ must be recognised as representations induced from subgroups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_nonempty_ind_res_iso_tensor_ofMulAction_quotient.lean

import Mathlib
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical

theorem Rep.nonempty_ind_res_iso_tensor_ofMulAction_quotient
    {k : Type} [CommRing k] {G : Type} [Group G] (D : Subgroup G) (M : Rep.{0} k G) :
    Nonempty (Rep.ind D.subtype (Rep.res D.subtype M) ≅ M ⊗ Rep.ofMulActionFinsupp k G (G ⧸ D)) := by sorry
