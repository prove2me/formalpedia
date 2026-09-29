-- Prove2me | Theorems.Thm_Rep_tateH0Cores_comp_tateH0Res
-- name    : Rep.tateH0Cores_comp_tateH0Res
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/7e0eecb8-a2be-5b52-b6b9-e630c2a4f69b
-- title:
--   Corestriction after restriction is multiplication by the index on ̂ H⁰
-- statement:
--   Let $k$ be a commutative ring, $G$ a group with a `Fintype` structure, $S \le G$ a subgroup that is likewise equipped with a `Fintype` structure, and $A$ a $k$-linear representation of $G$ (an object of `Rep k G`, with underlying module in universe $w$). Here $\hat H^0$ of a representation $\rho$ is the quotient module [`Representation.tateH0`](def/GroupCohomology_TateCohomology.html#L45), namely the $\rho$-invariants modulo the range of [`Representation.normBar`](def/GroupCohomology_TateCohomology.html#L40), and two maps between the degree-zero Tate groups of $A$ and of its restriction `Rep.res S.subtype A` along $S \hookrightarrow G$ are in play: [`Rep.tateH0Res`](def/GroupCohomology_TateResCor.html#L218), induced on quotients by the inclusion of the $G$-invariants into the $S$-invariants, and [`Rep.tateH0Cores`](def/GroupCohomology_TateResCor.html#L221), induced on quotients by `cosetNormInvariants`, i.e. by the coset-norm map $a \mapsto \sum_{q \in G/S} \rho(\tilde q)\,a$ (summed over chosen representatives $\tilde q$ of the cosets) corestricted to the $G$-invariants. The assertion is an equality of $k$-linear endomorphisms of $\hat H^0(G,A)$: the composite of [`Rep.tateH0Res`](def/GroupCohomology_TateResCor.html#L218) followed by [`Rep.tateH0Cores`](def/GroupCohomology_TateResCor.html#L221) equals the image of the index $[G:S]$ in $k$ times the identity map.
--
--   This is the classical identity $\mathrm{Cor}^G_S \circ \mathrm{Res}^G_S = [G:S]$, here in Tate degree $0$ for a representation over an arbitrary commutative ring. It is used in the proof that Tate cohomology vanishes once it vanishes for all Sylow subgroups ([`Rep.isZero_tateCohomology_of_forall_sylow`](thm.html#Rep.isZero_tateCohomology_of_forall_sylow)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_tateH0Cores_comp_tateH0Res.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateResCor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u v w
open CategoryTheory Rep

theorem Rep.tateH0Cores_comp_tateH0Res {k : Type u} {G : Type v} [CommRing k] [Group G] [Fintype G]
    (S : Subgroup G) [Fintype S] (A : Rep.{w} k G) :
    Rep.tateH0Cores S A ∘ₗ Rep.tateH0Res S A = (S.index : k) • LinearMap.id := by sorry
