-- Prove2me | Theorems.Thm_Rep_exact_tateMap_tateDelta
-- name    : Rep.exact_tateMap_tateDelta
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/acd103fe-3499-5a87-8edb-8996bc126b89
-- title:
--   Exactness of the Tate sequence at ̂ Hⁿ(X₃)
-- statement:
--   Let $k$ be a commutative ring and $G$ a finite group, and let $X$ be a short complex $X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3$ in the category of $k$-linear representations of $G$ which is short exact (`hX`), i.e. $f$ is a monomorphism, $g$ an epimorphism and the complex exact in the middle. Let $n$ be an arbitrary integer. The assertion is that the pair of $k$-linear maps underlying $\mathrm{tateMap}\ g\ n : \hat H^n(X_2) \to \hat H^n(X_3)$ and the connecting map $\mathrm{tate\delta}\ hX\ n : \hat H^n(X_3) \to \hat H^{n+1}(X_1)$ is exact in the sense of `Function.Exact`: the range of the first equals the kernel of the second. Here Tate cohomology $\hat H^n(A)$ is defined by cases: $\mathrm{groupCohomology}\ A\ (n)$ for $n \ge 1$; for $n = 0$ the quotient of the $G$-invariants of $A$ by the range of the norm map $\rho.\mathrm{normBar}$; for $n = -1$ the kernel of the induced norm map on the coinvariants of $A$; and $\mathrm{groupHomology}\ A\ (-n-1)$ for $n \le -2$. Correspondingly $\mathrm{tateMap}\ g\ n$ is the map induced by $g$ on group cohomology in degrees $\ge 1$, the map induced by $g$ on invariants passed to the quotient in degree $0$, the restriction to the kernel of the norm of the map induced by $g$ on coinvariants in degree $-1$, and the map induced by $g$ on group homology in degrees $\le -2$.
--
--   This is exactness at the middle term of the long exact sequence of Tate cohomology attached to a short exact sequence of representations of a finite group, uniformly in all integer degrees. It is used in the computations of vanishing of Tate cohomology (for $p$-groups, for internal homs and for restricted tensor products) and in the criterion for the connecting map to be bijective.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exact_tateMap_tateDelta.lean

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

theorem Rep.exact_tateMap_tateDelta {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (n : ℤ) :
    Function.Exact (Rep.tateMap X.g n).hom (Rep.tateδ hX n).hom := by sorry
