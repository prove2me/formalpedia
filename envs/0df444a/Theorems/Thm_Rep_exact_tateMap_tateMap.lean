-- Prove2me | Theorems.Thm_Rep_exact_tateMap_tateMap
-- name    : Rep.exact_tateMap_tateMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/c3447019-ae4a-5af6-aeeb-724b0f22ff95
-- title:
--   Exactness of Tate cohomology functors on a short exact sequence
-- statement:
--   Let $k$ be a commutative ring and $G$ a finite group, and let $X$ be a short complex $X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3$ in the category $\mathrm{Rep}\,k\,G$ of $k$-linear representations of $G$, assumed short exact (`hX`), i.e. $f$ is a monomorphism, $g$ an epimorphism and the complex exact. Then for every integer $n$ the sequence of $k$-modules obtained by applying the degree-$n$ Tate construction
--   $$\hat H^n(X_1) \xrightarrow{f_*} \hat H^n(X_2) \xrightarrow{g_*} \hat H^n(X_3)$$
--   is exact at the middle term, in the sense that the range of the underlying $k$-linear map of [`Rep.tateMap X.f n`](def/GroupCohomology_TateShiftMaps.html#L17) equals the kernel of that of [`Rep.tateMap X.g n`](def/GroupCohomology_TateShiftMaps.html#L17). Here [`Rep.tateCohomology`](def/GroupCohomology_TateCohomology.html#L140) is defined by cases: in degrees $n+1 \ge 1$ it is group cohomology $H^{n+1}(G,-)$, in degree $0$ the quotient of the invariants by the image of the map `normBar`, in degree $-1$ the kernel of `normBar` (a submodule of the coinvariants), and in degrees $-n-2 \le -2$ group homology $H_{n+1}(G,-)$; correspondingly [`Rep.tateMap`](def/GroupCohomology_TateShiftMaps.html#L17) is the functorial map induced by $\varphi$ in cohomology, the map induced on the degree-$0$ quotient by the map on invariants, the restriction of the map on coinvariants to the kernels of `normBar`, and the functorial map in homology.
--
--   This is exactness at the middle term of the long exact sequence in Tate cohomology attached to a short exact sequence of representations of a finite group, assembled uniformly over all integer degrees. It is used in the proof that the Tate cohomology of an internal-hom object vanishes for $p$-groups ([`Rep.isZero_tateCohomology_ihom_of_isPGroup`](thm.html#Rep.isZero_tateCohomology_ihom_of_isPGroup)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exact_tateMap_tateMap.lean

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

theorem Rep.exact_tateMap_tateMap {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (n : ℤ) :
    Function.Exact (Rep.tateMap X.f n).hom (Rep.tateMap X.g n).hom := by sorry
