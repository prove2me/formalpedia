-- Prove2me | Theorems.Thm_Rep_exact_tateDeltaNeg2_tateHneg1Map
-- name    : Rep.exact_tateDeltaNeg2_tateHneg1Map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/b43309ec-65ff-5694-983b-45b755c0ba15
-- title:
--   Exactness at ̂ H⁻¹ of the Tate sequence
-- statement:
--   Let $k$ be a commutative ring, $G$ a finite group, and let $X$ be a short complex $X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3$ in the category of $k$-linear representations of $G$, assumed short exact (`hX`). For a representation $A$, write $A_G$ for its coinvariants and $\bar N_A : A_G \to A^G$ for the $k$-linear map induced on coinvariants by the norm $a \mapsto \sum_{h \in G} h\cdot a$ (the map `Rep.normBar`, obtained by factoring the norm-to-invariants map through the coinvariants); then $\hat H^{-1}(G,A)$ is by definition the $k$-submodule $\ker \bar N_A \subseteq A_G$, and for a morphism $\varphi : A \to B$ the map [`Rep.tateHneg1Map`](def/GroupCohomology_TateCohomology.html#L99) $\varphi$ is the restriction to these kernels of the functorially induced map $A_G \to B_G$. The assertion is that the pair consisting of the connecting map [`Rep.tateδneg2 hX`](def/GroupCohomology_TateSeam.html#L165), whose target is $\hat H^{-1}(G,X_1)$ and whose source is the first group homology of $X_3$, followed by [`Rep.tateHneg1Map X.f`](def/GroupCohomology_TateCohomology.html#L99) $: \hat H^{-1}(G,X_1) \to \hat H^{-1}(G,X_2)$, is exact in the sense of `Function.Exact`: an element $x \in \ker \bar N_{X_1}$ is killed by the map induced by $f$ if and only if $x$ lies in the image of [`Rep.tateδneg2 hX`](def/GroupCohomology_TateSeam.html#L165).
--
--   This is exactness of the Tate long exact sequence of the short exact sequence $0 \to X_1 \to X_2 \to X_3 \to 0$ at the vertex $\hat H^{-1}(G,X_1)$, where the sequence is still in its homological range and the incoming map comes from $H_1(G,X_3)$. It is one of the vertex-by-vertex exactness statements assembled by [`Rep.exact_tateDelta_tateMap`](thm.html#Rep.exact_tateDelta_tateMap) and used in [`Rep.nonempty_tateCohomology_iso_of_shortExact_of_isZero`](thm.html#Rep.nonempty_tateCohomology_iso_of_shortExact_of_isZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exact_tateDeltaNeg2_tateHneg1Map.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.exact_tateDeltaNeg2_tateHneg1Map {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) :
    Function.Exact (Rep.tateδneg2 hX) (Rep.tateHneg1Map X.f) := by sorry
