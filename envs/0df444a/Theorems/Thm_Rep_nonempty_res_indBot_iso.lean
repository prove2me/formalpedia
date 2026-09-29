-- Prove2me | Theorems.Thm_Rep_nonempty_res_indBot_iso
-- name    : Rep.nonempty_res_indBot_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/23037594-c3eb-51fc-b49f-cdf452920dde
-- title:
--   Mackey: Res_S Ind₁^G A ≅ Ind₁^S(bigoplus_{G/S}A)
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, $S$ a subgroup of $G$ and $A$ a $k$-linear representation of $G$ (objects of `Rep k G`, all data in one universe). Write $A.\mathrm{indBot}$ for the representation obtained by inducing along the inclusion $(\bot : \mathrm{Subgroup}\ G) \hookrightarrow G$ the restriction of $A$ to the trivial subgroup; concretely, this is the $G$-representation $k[G] \otimes_k A$ built as the coinvariants of the tensor product of the left regular representation with the restricted action, with only the underlying $k$-module of $A$ entering. The theorem asserts that the type of isomorphisms in `Rep k S` between the restriction of $A.\mathrm{indBot}$ along the inclusion $S \hookrightarrow G$ and the analogous induction-from-$\bot$ applied to the $S$-representation `Rep.trivial k S ((G ⧸ S) →₀ A)` — the finitely supported functions from the coset space $G/S$ to $A$ with trivial $S$-action — is nonempty. Thus the conclusion is the bare existence of such an isomorphism of $S$-representations, no particular isomorphism being named in the statement.
--
--   This is the elementary case of the Mackey decomposition: $k[G]$ is free as a $k[S]$-module on a set of representatives for $G/S$, so a module induced from the trivial subgroup of $G$ restricts to a module induced from the trivial subgroup of $S$. It is used to show that the Tate cohomology of such induced modules vanishes over subgroups ([`Rep.isZero_tateCohomology_res_indBot`](thm.html#Rep.isZero_tateCohomology_res_indBot)), which is what makes dimension shifting compatible with restriction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_nonempty_res_indBot_iso.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.nonempty_res_indBot_iso {k G : Type u} [CommRing k] [Group G]
    (S : Subgroup G) (A : Rep.{u} k G) :
    Nonempty (Rep.res S.subtype A.indBot ≅ (Rep.trivial k S ((G ⧸ S) →₀ A)).indBot) := by sorry
