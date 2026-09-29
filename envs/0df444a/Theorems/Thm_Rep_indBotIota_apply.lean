-- Prove2me | Theorems.Thm_Rep_indBotIota_apply
-- name    : Rep.indBotIota_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/670f8217-cbbd-5784-85d3-7a1a0d9828f9
-- title:
--   The unit A → Ind₁^GRes₁^G A as a sum over G
-- statement:
--   Let $k$ be a commutative ring and $G$ a finite group, and let $A$ be a $k$-linear representation of $G$. Write $A.\mathrm{indBot}$ for the representation $\operatorname{Ind}_{\iota}\operatorname{Res}_{\iota}A$ obtained by restricting $A$ along the inclusion $\iota\colon\{1\}\hookrightarrow G$ of the trivial subgroup and then inducing along $\iota$, and for $g\in G$ let $A.\mathrm{indBotMk}\,g\colon A\to A.\mathrm{indBot}$ be the $k$-linear map `Representation.IndV.mk` at $g$ for the trivial subgroup, i.e. $a\mapsto[g\otimes a]$. The assertion is that for every $a\in A$ the underlying $k$-linear map of the morphism [`Rep.indBotι A`](def/GroupCohomology_TateDimensionShift.html#L54) $\colon A\to A.\mathrm{indBot}$ sends $a$ to
--   $$\sum_{g\in G} A.\mathrm{indBotMk}\,g\,(A.\rho\,g\,a),$$
--   the sum being over all elements of the finite group $G$; equivalently, $a\mapsto\sum_{g\in G}[\,g\otimes g a\,]$. Finiteness of $G$ is what makes this sum, and the identification of the induced with the coinduced representation used in its proof, available.
--
--   This computes the unit of the adjunction $\operatorname{Res}\dashv\operatorname{Ind}$ for the trivial subgroup in explicit coordinates, exhibiting it as the "norm"-type map $a\mapsto\sum_g[g\otimes ga]$. It is the input to [`Rep.indBotr_indBotIota`](thm.html#Rep.indBotr_indBotIota) and serves the dimension-shifting arguments in Tate cohomology, where $A$ is embedded into the induced (equivalently coinduced) representation $\operatorname{Ind}_1^G\operatorname{Res}_1^G A$, whose Tate cohomology vanishes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_indBotIota_apply.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.indBotIota_apply {k G : Type u} [CommRing k] [Group G] [Fintype G] (A : Rep.{u} k G) (a : A) :
    (Rep.indBotι A).hom a = ∑ g : G, A.indBotMk g (A.ρ g a) := by sorry
