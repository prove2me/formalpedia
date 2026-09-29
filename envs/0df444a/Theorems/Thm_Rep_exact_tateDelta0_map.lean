-- Prove2me | Theorems.Thm_Rep_exact_tateDelta0_map
-- name    : Rep.exact_tateDelta0_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/025bafd6-f341-5486-a6e0-f13a6cf38d7b
-- title:
--   Exactness of ̂ H⁰(C) → H¹(A) → H¹(B)
-- statement:
--   Let $k$ be a commutative ring, let $G$ be a finite group, and let $X$ be a short complex $X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3$ in the category $\mathrm{Rep}\,k\,G$ of $k$-linear representations of $G$, assumed short exact (`hX`), i.e. $f$ is a monomorphism, $g$ an epimorphism and the complex exact at $X_2$. The assertion is that the pair of $k$-linear maps
--   $$\hat H^0(G, X_3) \longrightarrow H^1(G, X_1) \longrightarrow H^1(G, X_2)$$
--   is exact in the sense of `Function.Exact`: an element of $H^1(G,X_1)$ is killed by the second map if and only if it lies in the image of the first. Here the first map is the project's connecting map [`Rep.tateδ₀ hX`](def/GroupCohomology_TateSeam.html#L140) out of the Tate group $\hat H^0(G,X_3)$, the quotient of the invariants of $X_3$ by the image of the norm, which on the class of an invariant $z$ is the value of Mathlib's connecting homomorphism $\delta\colon H^0(G,X_3) \to H^1(G,X_1)$ at the image of $z$ under the inverse of `groupCohomology.H0Iso`; the second map is the underlying $k$-linear map of $(\text{groupCohomology.functor } k\,G\,1).\mathrm{map}\ f$, that is, the map on $H^1$ induced by $f$.
--
--   This is the segment $\hat H^0(G,C) \to H^1(G,A) \to H^1(G,B)$ of the long exact sequence of Tate cohomology attached to a short exact sequence of representations of a finite group, i.e. exactness at the place where Tate cohomology in degree $0$ meets ordinary cohomology in degree $1$. It is used in assembling the full Tate long exact sequence ([`Rep.exact_tateDelta_tateMap`](thm.html#Rep.exact_tateDelta_tateMap)) and in the construction of isomorphisms of Tate cohomology groups from short exact sequences with a vanishing term.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exact_tateDelta0_map.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.exact_tateDelta0_map {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) :
    Function.Exact (Rep.tateδ₀ hX) ((groupCohomology.functor k G 1).map X.f).hom := by sorry
