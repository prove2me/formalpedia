-- Prove2me | Theorems.Thm_Rep_exact_tateHneg1Map_tateHneg1Map
-- name    : Rep.exact_tateHneg1Map_tateHneg1Map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/a7a3f2f8-a50d-54ed-9525-5bd180d6700f
-- title:
--   Exactness at the middle of Tate widehat H⁻¹
-- statement:
--   Let $k$ be a commutative ring and $G$ a group with finitely many elements, and let $X$ be a short complex $X_1 \xrightarrow{f} X_2 \xrightarrow{g} X_3$ in the category of $k$-linear representations of $G$ (so $f$ followed by $g$ is zero) which is short exact, i.e. $f$ is a monomorphism, $g$ an epimorphism and the complex exact at $X_2$. For a representation $A$ with action $\rho$, the project's degree $-1$ Tate group [`Rep.tateHneg1`](def/GroupCohomology_TateCohomology.html#L59) $A$ is the kernel of the $k$-linear map $\bar N \colon A_G \to A^G$ obtained by descending the norm map $a \mapsto \sum_{h \in G} \rho(h)a$, viewed as a map into the invariants, along the quotient $A \to A_G$ onto the coinvariants; for a morphism $\varphi$ of representations, [`Rep.tateHneg1Map`](def/GroupCohomology_TateCohomology.html#L99) $\varphi$ is the restriction of the induced map on coinvariants to these kernels. The assertion is that the pair of maps [`Rep.tateHneg1Map X.f`](def/GroupCohomology_TateCohomology.html#L99) and [`Rep.tateHneg1Map X.g`](def/GroupCohomology_TateCohomology.html#L99) is exact in the sense of `Function.Exact`: for every $y$ in the kernel of $\bar N$ on $(X_2)_G$, the class $g_*y$ vanishes in $\widehat H^{-1}$ of $X_3$ if and only if $y = f_*(w)$ for some $w$ in the kernel of $\bar N$ on $(X_1)_G$.
--
--   This is the exactness at the middle term of the degree $-1$ part of the Tate cohomology long exact sequence attached to a short exact sequence of representations of a finite group. It is used by [`Rep.exact_tateMap_tateMap`](thm.html#Rep.exact_tateMap_tateMap), the companion statement in degree $0$, within the construction of the Tate long exact sequence.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exact_tateHneg1Map_tateHneg1Map.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u v w
open CategoryTheory Rep

theorem Rep.exact_tateHneg1Map_tateHneg1Map {k G : Type*} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact) :
    Function.Exact (Rep.tateHneg1Map X.f) (Rep.tateHneg1Map X.g) := by sorry
