-- Prove2me | Theorems.Thm_Rep_tateDelta_naturality
-- name    : Rep.tateDelta_naturality
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/90bc8f32-def9-55da-b918-c54b70b22c55
-- title:
--   Naturality of the Tate connecting maps in all degrees
-- statement:
--   Let $k$ be a commutative ring and $G$ a finite group. Let $X$ and $Y$ be short complexes in the category $\mathrm{Rep}\,k\,G$ of $k$-linear representations of $G$, assumed short exact (`hX`, `hY`), let $\tau : X \to Y$ be a morphism of short complexes, with components $\tau_1, \tau_2, \tau_3$ on the three terms, and let $n \in \mathbb{Z}$. The assertion is the equality of the two composites from $X_3$'s Tate cohomology in degree $n$ to $Y_1$'s Tate cohomology in degree $n+1$: the connecting map [`Rep.tateδ hX n`](def/GroupCohomology_TateShiftMaps.html#L32) followed by [`Rep.tateMap τ.τ₁ (n+1)`](def/GroupCohomology_TateShiftMaps.html#L17) equals [`Rep.tateMap τ.τ₃ n`](def/GroupCohomology_TateShiftMaps.html#L17) followed by [`Rep.tateδ hY n`](def/GroupCohomology_TateShiftMaps.html#L32). Here [`Rep.tateCohomology A`](def/GroupCohomology_TateCohomology.html#L140) is defined degreewise: $\mathrm{groupCohomology}\,A\,(m+1)$ in degrees $m+1 \ge 1$, the quotient `A.tateH0` of the $G$-invariants by the image of the norm map in degree $0$, the submodule `A.tateHneg1` of elements of the coinvariants killed by the induced norm in degree $-1$, and $\mathrm{groupHomology}\,A\,(m+1)$ in degrees $-(m+2) \le -2$; correspondingly [`Rep.tateMap φ`](def/GroupCohomology_TateShiftMaps.html#L17) is `groupCohomology.map (MonoidHom.id G) φ` in positive degrees, the maps `tateH0Map φ` and `tateHneg1Map φ` induced by $\varphi$ on invariants modulo norms and on norm-killed coinvariants in degrees $0$ and $-1$, and `groupHomology.map (MonoidHom.id G) φ` in degrees $\le -2$.
--
--   This is the naturality of the connecting homomorphism in the long exact sequence of Tate cohomology of a finite group, stated uniformly over all integers $n$. It is used throughout the Tate-cohomological part of the development, in particular in the construction and characterisation of the Tate cup product (associativity, duality pairings) and in dévissage arguments reducing statements in one degree to neighbouring degrees.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_tateDelta_naturality.lean

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

theorem Rep.tateDelta_naturality {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X Y : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (hY : Y.ShortExact) (τ : X ⟶ Y) (n : ℤ) :
    Rep.tateδ hX n ≫ Rep.tateMap τ.τ₁ (n + 1) = Rep.tateMap τ.τ₃ n ≫ Rep.tateδ hY n := by sorry
