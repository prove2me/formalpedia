-- Prove2me | Theorems.Thm_Rep_exact_tateDeltaNeg1_tateH0Map
-- name    : Rep.exact_tateDeltaNeg1_tateH0Map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/b2488a3f-6e83-58d9-90a8-f17e6eb1e107
-- title:
--   Exactness at ̂ H⁰(A) of the Tate sequence
-- statement:
--   Let $k$ be a commutative ring and $G$ a finite group, and let $X$ be a short complex $X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3$ in the category of representations of $G$ over $k$ (on $k$-modules in a universe $w$), together with a witness $hX$ that $X$ is short exact in the sense of `ShortComplex.ShortExact`, i.e. $f$ is a monomorphism, $g$ an epimorphism and the complex exact. For a representation $A$, the group $A$`.tateH0` is by definition the quotient $k$-module $A.\rho$`.invariants` $/$ `LinearMap.range` $A.\rho$`.normBar`, the $G$-invariants modulo the image of the norm map factored through coinvariants, and for a morphism $\varphi : A \to B$ the map [`Rep.tateH0Map`](def/GroupCohomology_TateCohomology.html#L93) $\varphi$ is the $k$-linear map on these quotients induced by the restriction of $\varphi$ to invariants (the action of the invariants functor on $\varphi$), which is legitimate because that restriction carries the range of `normBar` into the range of `normBar`. The assertion is that the pair of $k$-linear maps [`Rep.tateδneg1 hX`](def/GroupCohomology_TateSeam.html#L104), the degree $-1$ connecting map attached to $hX$ with target $X_1$`.tateH0`, and [`Rep.tateH0Map X.f`](def/GroupCohomology_TateCohomology.html#L93) is exact as a pair of functions: for every class $y \in X_1$`.tateH0`, one has [`Rep.tateH0Map X.f`](def/GroupCohomology_TateCohomology.html#L93) $y = 0$ if and only if $y$ lies in the image of [`Rep.tateδneg1 hX`](def/GroupCohomology_TateSeam.html#L104).
--
--   This is the exactness at $\hat H^{0}(G,X_1)$ of the long exact sequence of Tate cohomology attached to a short exact sequence of representations of a finite group, in the form 'kernel equals image' for the underlying $k$-linear maps. It is one of the segment-by-segment exactness statements assembled by [`Rep.exact_tateDelta_tateMap`](thm.html#Rep.exact_tateDelta_tateMap) and used in [`Rep.nonempty_tateCohomology_iso_of_shortExact_of_isZero`](thm.html#Rep.nonempty_tateCohomology_iso_of_shortExact_of_isZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exact_tateDeltaNeg1_tateH0Map.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u v w
open CategoryTheory Rep

theorem Rep.exact_tateDeltaNeg1_tateH0Map {k : Type u} {G : Type v} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{w} k G)} (hX : X.ShortExact) :
    Function.Exact (Rep.tateδneg1 hX) (Rep.tateH0Map X.f) := by sorry
