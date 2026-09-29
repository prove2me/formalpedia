-- Prove2me | Theorems.Thm_Rep_bijective_tateDelta_dimShiftDown
-- name    : Rep.bijective_tateDelta_dimShiftDown
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/69ec6291-32f0-5de4-b8fd-dc3085acf360
-- title:
--   Dimension shifting: δⁿ is bijective for the sequence 0→ A''→ Ind A→ A→ 0
-- statement:
--   Let $k$ be a commutative ring, $G$ a finite group and $A$ an object of `Rep k G`, i.e. a $k$-linear representation of $G$. Consider the short complex `A.dimShiftDown` in `Rep k G`: its middle term is `A.indBot`, the representation induced along the inclusion $\bot \hookrightarrow G$ of the trivial subgroup from the restriction of $A$ to $\bot$; its third term is $A$, with structure map the canonical morphism `indBotπ A : A.indBot ⟶ A`; its first term is the subrepresentation of `A.indBot` carried by the kernel of (the underlying linear map of) `indBotπ A`, with structure map the inclusion of that submodule, so that the composite of the two maps is zero. Assume `hA` that this short complex is short exact. Then, for every integer $n$, the underlying map of the connecting morphism [`Rep.tateδ hA n`](def/GroupCohomology_TateShiftMaps.html#L32) in degree $n$ attached to this short exact sequence — the map $\hat H^{n}(G,A) \to \hat H^{n+1}(G,A'')$ on Tate cohomology, where $A''$ denotes the kernel term — is bijective.
--
--   This is the dimension-shifting isomorphism for Tate cohomology of a finite group, here in map-level form: the connecting map of the sequence $0 \to A'' \to \mathrm{Ind}_{\bot}^{G}\mathrm{Res}_{\bot}A \to A \to 0$ is an isomorphism in every degree, so that Tate cohomology in degree $n$ of $A$ is identified with degree $n+1$ of $A''$. It is used in the construction and in the injectivity and vanishing properties of the Tate cup product pairing against the character dual, via [`Rep.exists_isTateCupProduct`](thm.html#Rep.exists_isTateCupProduct), [`Rep.IsTateCupProduct.injective_cupEv_characterDual`](thm.html#Rep.IsTateCupProduct.injective_cupEv_characterDual) and [`Rep.IsTateCupProduct.cupEv_characterDual_eq_zero`](thm.html#Rep.IsTateCupProduct.cupEv_characterDual_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_bijective_tateDelta_dimShiftDown.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateDimensionShift
import Definitions.Def_GroupCohomology_TateShiftMaps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.bijective_tateDelta_dimShiftDown {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A : Rep.{u} k G) (hA : A.dimShiftDown.ShortExact) (n : ℤ) :
    Function.Bijective (Rep.tateδ hA n).hom := by sorry
