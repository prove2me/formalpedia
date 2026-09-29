-- Prove2me | Theorems.Thm_Rep_indBot_rho_indBotMk
-- name    : Rep.indBot_rho_indBotMk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/182c1c7c-46de-52d2-aa23-fc65a2d93129
-- title:
--   Action on Ind₁^G Res₁^G A on elementary tensors
-- statement:
--   Let $k$ be a commutative ring, $G$ a group and $A$ a $k$-linear representation of $G$ (an object of `Rep k G`). Write $A.\mathtt{indBot}$ for the representation obtained by restricting $A$ along the inclusion of the trivial subgroup $\bot \le G$ and then inducing back along that same inclusion, i.e. $\mathrm{Ind}_{\bot}^{G}\,\mathrm{Res}^{G}_{\bot}A$, and for $g \in G$ write $A.\mathtt{indBotMk}\,g$ for the $k$-linear map from the underlying module of $A$ into this induced representation sending $a$ to the elementary tensor indexed by $g$ (Mathlib's `Representation.IndV.mk` for the restriction of $A$ along $\bot \hookrightarrow G$, at the group element $g$). The assertion is that for all $g, h \in G$ and all $a \in A$, applying the representation map of $A.\mathtt{indBot}$ at $g$ to the elementary tensor $A.\mathtt{indBotMk}\,h\,a$ yields the elementary tensor $A.\mathtt{indBotMk}\,(h g^{-1})\,a$; in the customary notation, $g \cdot [\,h \otimes a\,] = [\,h g^{-1} \otimes a\,]$, so that $G$ acts on the index group by right translation through the inverse.
--
--   This is the defining formula for the action on an induced representation, specialised to induction from the trivial subgroup and recorded for the generators $A.\mathtt{indBotMk}\,h\,a$ used throughout the dimension-shifting constructions in Tate cohomology. It is the computational basis for the vanishing results for Tate cohomology of $\mathrm{Ind}_\bot^G\,\mathrm{Res}^G_\bot A$ and its tensor and internal-hom variants, such as [`Rep.isZero_tateCohomology_ihom_indBot`](thm.html#Rep.isZero_tateCohomology_ihom_indBot) and [`Rep.isZero_tateCohomology_indBot_tensor`](thm.html#Rep.isZero_tateCohomology_indBot_tensor).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_indBot_rho_indBotMk.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.indBot_rho_indBotMk {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (g h : G) (a : A) :
    A.indBot.ρ g (A.indBotMk h a) = A.indBotMk (h * g⁻¹) a := by sorry
