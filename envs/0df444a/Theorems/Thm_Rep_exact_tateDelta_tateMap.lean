-- Prove2me | Theorems.Thm_Rep_exact_tateDelta_tateMap
-- name    : Rep.exact_tateDelta_tateMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/fd0cd8a6-2d9c-5f9a-94f3-29e41a5cee0d
-- title:
--   Exactness of the Tate long exact sequence at ̂ Hⁿ⁺¹(X₁)
-- statement:
--   Let $k$ be a commutative ring and $G$ a finite group, and let $X$ be a short complex $X_1 \xrightarrow{f} X_2 \to X_3$ of $k$-linear representations of $G$ which is short exact (`hX`). Let $n$ be an arbitrary integer. The assertion is that the $k$-linear map underlying the connecting morphism [`Rep.tateδ hX n`](def/GroupCohomology_TateShiftMaps.html#L32), from the degree-$n$ Tate cohomology of $X_3$ to the degree-$(n+1)$ Tate cohomology of $X_1$, followed by the map underlying [`Rep.tateMap X.f (n+1)`](def/GroupCohomology_TateShiftMaps.html#L17) on degree-$(n+1)$ Tate cohomology induced by $f$, is exact in the sense of `Function.Exact`: the image of the first coincides with the kernel of the second. Here the Tate groups and the induced maps are those defined by cases on the degree: in degrees $m+1 \ge 1$ they are $H^{m+1}(G,-)$ with the map `groupCohomology.map` along the identity of $G$ and $f$; in degree $0$ the quotient of the invariants by the image of the norm map `normBar`, with the map induced by functoriality of invariants; in degree $-1$ the kernel of `normBar` on the coinvariants, with the map induced by functoriality of coinvariants; and in degrees $-(m+2) \le -2$ the homology $H_{m+1}(G,-)$ with the map `groupHomology.map` along the identity of $G$ and $f$.
--
--   This is one of the three exactness assertions making up the long exact sequence of Tate cohomology attached to a short exact sequence of representations of a finite group, here exactness at $\hat H^{n+1}(G,X_1)$, uniformly in $n \in \mathbb{Z}$. It is used in the study of vanishing of Tate cohomology, for instance by [`Rep.bijective_tateDelta_of_isZero`](thm.html#Rep.bijective_tateDelta_of_isZero), [`Rep.exists_shortExact_free_of_forall_isZero`](thm.html#Rep.exists_shortExact_free_of_forall_isZero) and [`Rep.isZero_tateCohomology_ihom_of_isPGroup`](thm.html#Rep.isZero_tateCohomology_ihom_of_isPGroup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exact_tateDelta_tateMap.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.exact_tateDelta_tateMap {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (n : ℤ) :
    Function.Exact (Rep.tateδ hX n).hom (Rep.tateMap X.f (n + 1)).hom := by sorry
