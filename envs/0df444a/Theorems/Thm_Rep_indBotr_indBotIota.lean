-- Prove2me | Theorems.Thm_Rep_indBotr_indBotIota
-- name    : Rep.indBotr_indBotIota
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/9af40b83-b964-5520-a597-ffa54ecf670e
-- title:
--   The unit A → Ind_{mathbf 1}^GResA admits a k-linear retraction
-- statement:
--   Fix a universe $u$, a commutative ring $k$ and a finite group $G$, and let $A$ be an object of $\mathrm{Rep}_{k}(G)$, i.e. a $k$-module with a $k$-linear $G$-action $\rho$. Here $A.\mathrm{indBot}$ denotes $\mathrm{Rep.ind}$ along the inclusion of the trivial subgroup $\bot \le G$, applied to the restriction of $A$ to $\bot$; its elements are represented by classes of tensors $f \otimes a$ with $f \in k[G]$ and $a \in A$, taken in the relevant coinvariants. The map [`Rep.indBotr`](def/GroupCohomology_TateDimensionShift.html#L32) is the $k$-linear map $A.\mathrm{indBot} \to A$ obtained from the bilinear map $(f,a) \mapsto f(1)\cdot a$, where $f \in k[G]$ is viewed as a finitely supported function on $G$ and evaluated at the identity; this descends to the coinvariants because $\bot$ is a subsingleton. The morphism [`Rep.indBotι A`](def/GroupCohomology_TateDimensionShift.html#L54) is the unit $A \to A.\mathrm{indBot}$, whose underlying $k$-linear map sends $a$ to $\sum_{g \in G} [\,g \otimes \rho(g)a\,]$. The assertion is that for every $a \in A$ one has $\mathrm{indBotr}\big(\iota(a)\big) = a$, i.e. [`Rep.indBotr`](def/GroupCohomology_TateDimensionShift.html#L32) is a retraction of the underlying $k$-linear map of [`Rep.indBotι`](def/GroupCohomology_TateDimensionShift.html#L54).
--
--   This is the $k$-linear splitting used in dimension shifting for Tate cohomology: it exhibits $A$ as a $k$-module direct summand of $\operatorname{Ind}_{\mathbf 1}^{G}\operatorname{Res}_{\mathbf 1}^{G} A$ (the splitting being $k$-linear, not $k[G]$-linear) and in particular shows that the unit is injective. It is used in the construction and the formal properties of the Tate cup product, such as its associativity, commutativity and the vanishing of cup evaluation against the character dual.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_indBotr_indBotIota.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.indBotr_indBotIota {k G : Type u} [CommRing k] [Group G] [Fintype G] (A : Rep.{u} k G) (a : A) :
    A.indBotr ((Rep.indBotι A).hom a) = a := by sorry
