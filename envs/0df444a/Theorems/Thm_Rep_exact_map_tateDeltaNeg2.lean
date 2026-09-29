-- Prove2me | Theorems.Thm_Rep_exact_map_tateDeltaNeg2
-- name    : Rep.exact_map_tateDeltaNeg2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/5c3122f2-6b56-5352-8088-0a9f9cde5ce7
-- title:
--   Exactness of H₁(B)→ H₁(C)→ ̂ H⁻¹(A) at H₁(C)
-- statement:
--   Let $k$ be a commutative ring and $G$ a group equipped with a `Fintype` instance, so finite, and let $X$ be a short complex $X_1 \to X_2 \to X_3$ in the category $\mathrm{Rep}\,k\,G$ of $k$-linear representations of $G$, assumed short exact in the sense of `ShortComplex.ShortExact` (the first map a monomorphism, the second an epimorphism, and the complex exact in the middle). The assertion is that the pair consisting of the underlying $k$-linear map of $(\mathrm{groupHomology.functor}\ k\ G\ 1).map\ X.g$, that is the map $H_1(G,X_2) \to H_1(G,X_3)$ induced in degree-one group homology by $X.g$, and the map [`Rep.tateδneg2 hX`](def/GroupCohomology_TateSeam.html#L165) out of $H_1(G,X_3)$ into the degree $-1$ Tate group attached to $X_1$, is exact as a pair of functions: for every $z \in H_1(G,X_3)$ one has [`Rep.tateδneg2 hX z = 0`](def/GroupCohomology_TateSeam.html#L165) if and only if $z$ lies in the image of the map induced by $X.g$. This is exactness at $H_1(G,X_3)$ of the segment $H_1(G,X_2) \to H_1(G,X_3) \to \hat H^{-1}(G,X_1)$.
--
--   This is one vertex of the long exact sequence of Tate cohomology of a finite group, at the place where ordinary homology $H_1 = \hat H^{-2}$ passes into the Tate groups $\hat H^{-1}$ and $\hat H^{0}$. It feeds the assembled exactness statement [`Rep.exact_tateMap_tateDelta`](thm.html#Rep.exact_tateMap_tateDelta) and the comparison of Tate cohomology along a short exact sequence with zero outer term, [`Rep.nonempty_tateCohomology_iso_of_shortExact_of_isZero`](thm.html#Rep.nonempty_tateCohomology_iso_of_shortExact_of_isZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exact_map_tateDeltaNeg2.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.exact_map_tateDeltaNeg2 {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) :
    Function.Exact ((groupHomology.functor k G 1).map X.g).hom (Rep.tateδneg2 hX) := by sorry
