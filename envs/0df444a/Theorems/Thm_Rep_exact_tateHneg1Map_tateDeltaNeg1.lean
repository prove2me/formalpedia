-- Prove2me | Theorems.Thm_Rep_exact_tateHneg1Map_tateDeltaNeg1
-- name    : Rep.exact_tateHneg1Map_tateDeltaNeg1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/260a5738-28da-5df0-b89e-cc39a1dc1c6c
-- title:
--   Exactness of the Tate sequence at ̂ H⁻¹ of the quotient
-- statement:
--   Let $k$ be a commutative ring, $G$ a finite group, and let $X$ be a short complex $X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3$ in the category of $k$-linear representations of $G$ which is short exact in the sense of `CategoryTheory.ShortComplex.ShortExact`. For a representation $\rho$ write $\bar N_\rho \colon \rho_{\mathrm{Coinv}} \to \rho^{G}$ for the $k$-linear map obtained by descending the norm $\sum_{g \in G} \rho(g)$, viewed as a map into the invariants, to the coinvariants ([`Representation.normBar`](def/GroupCohomology_TateCohomology.html#L40)), and set $\hat H^{-1}(\rho) = \ker \bar N_\rho$. For a morphism $\varphi$ of representations, [`Rep.tateHneg1Map`](def/GroupCohomology_TateCohomology.html#L99) $\varphi$ is the map on these kernels induced by the map on coinvariants coming from the coinvariants functor. The assertion is that the pair consisting of [`Rep.tateHneg1Map X.g`](def/GroupCohomology_TateCohomology.html#L99) $\colon \hat H^{-1}(X_2) \to \hat H^{-1}(X_3)$ and the connecting map [`Rep.tateδneg1 hX`](def/GroupCohomology_TateSeam.html#L104) out of $\hat H^{-1}(X_3)$ is exact in the sense of `Function.Exact`: an element $x \in \hat H^{-1}(X_3)$ satisfies [`Rep.tateδneg1 hX`](def/GroupCohomology_TateSeam.html#L104) $x = 0$ if and only if $x$ lies in the image of [`Rep.tateHneg1Map X.g`](def/GroupCohomology_TateCohomology.html#L99).
--
--   This is the exactness, at the $\hat H^{-1}$ term of the quotient, of the long exact sequence of Tate cohomology attached to a short exact sequence of representations of a finite group. It is used in the assembly of the full Tate long exact sequence ([`Rep.exact_tateMap_tateDelta`](thm.html#Rep.exact_tateMap_tateDelta)) and in the comparison of Tate cohomology groups of $X_1$ and $X_3$ when the middle term has vanishing Tate cohomology ([`Rep.nonempty_tateCohomology_iso_of_shortExact_of_isZero`](thm.html#Rep.nonempty_tateCohomology_iso_of_shortExact_of_isZero)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exact_tateHneg1Map_tateDeltaNeg1.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u v w
open CategoryTheory Rep

theorem Rep.exact_tateHneg1Map_tateDeltaNeg1 {k : Type u} {G : Type v} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{w} k G)} (hX : X.ShortExact) :
    Function.Exact (Rep.tateHneg1Map X.g) (Rep.tateδneg1 hX) := by sorry
