-- Prove2me | Theorems.Thm_Rep_exists_isTateCupProduct
-- name    : Rep.exists_isTateCupProduct
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/37e31e9e-fb95-5800-9b9a-dcb8cc7d73f1
-- title:
--   Existence of a cup product on Tate cohomology
-- statement:
--   Let $k$ be a commutative ring and $G$ a finite group, both taken in a single universe $u$. The assertion is that there exists a family $\smile$ of pairings — an element of [`Rep.TateCupFamily k G`](def/GroupCohomology_IsTateCupProduct.html#L20), that is, for every pair of $k$-linear representations $A,B$ of $G$ and every triple of integers $p,q,r$ with $p+q=r$ a $k$-bilinear map $\hat H^p(A)\times\hat H^q(B)\to\hat H^r(A\otimes B)$, where $\hat H^n(A)$ denotes `A.tateCohomology n`, equal to $H^{n}(G,A)$ for $n\ge 1$, to `A.tateH0` for $n=0$, to `A.tateHneg1` for $n=-1$ and to $H_{-n-1}(G,A)$ for $n\le -2$ — which satisfies [`Rep.IsTateCupProduct`](def/GroupCohomology_IsTateCupProduct.html#L28), i.e. the following four properties. First, in degrees $(p+1,q+1)$ with $p,q\ge 0$ the pairing agrees with any family on ordinary group cohomology satisfying [`groupCohomology.IsGradedCupProduct`](def/GroupCohomology_IsGradedCupProduct.html#L17) (the family computed on cocycle representatives by `cochainCup`). Secondly, naturality: for $\varphi\colon A\to A'$, $\psi\colon B\to B'$ one has $\mathrm{tateMap}(\varphi\otimes\psi)_r(x\smile y)=\mathrm{tateMap}(\varphi)_p(x)\smile \mathrm{tateMap}(\psi)_q(y)$, where [`Rep.tateMap`](def/GroupCohomology_TateShiftMaps.html#L17) is the degreewise functorial map ($\mathrm{groupCohomology.map}$, `tateH0Map`, `tateHneg1Map`, $\mathrm{groupHomology.map}$). Thirdly, for a short complex $X$ of representations that is short exact and $B$ such that $X\otimes B$ is short exact, $\delta_{X\otimes B}(x\smile y)=\delta_X(x)\smile y$ for $x\in\hat H^p(X_3)$, $y\in\hat H^q(B)$, with the Tate connecting maps [`Rep.tateδ`](def/GroupCohomology_TateShiftMaps.html#L32). Fourthly, symmetrically, for $A$ and short exact $X$ with $A\otimes X$ short exact, $\delta_{A\otimes X}(x\smile y)=(-1)^p\,(x\smile\delta_X(y))$, the sign being the image in $k$ of `Int.negOnePow p`.
--
--   This is the existence half of the construction of the Tate cup product $\hat H^p(G,A)\otimes\hat H^q(G,B)\to\hat H^{p+q}(G,A\otimes B)$ for a finite group $G$, characterised by agreement with the cup product of group cohomology in positive degrees, naturality and compatibility with connecting homomorphisms in each variable. It is used in the project's computations with Tate cohomology of relation modules, namely by [`Rep.exists_hom_relationModuleInt_forall_map_delta_eq`](thm.html#Rep.exists_hom_relationModuleInt_forall_map_delta_eq) and [`Rep.forall_map_delta_eq_zero_iff_exists_eq_sum_rho`](thm.html#Rep.forall_map_delta_eq_zero_iff_exists_eq_sum_rho).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exists_isTateCupProduct.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Definitions.Def_GroupCohomology_IsTateCupProduct

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory

theorem Rep.exists_isTateCupProduct {k G : Type u} [CommRing k] [Group G] [Fintype G] :
    ∃ cup : Rep.TateCupFamily k G, Rep.IsTateCupProduct cup := by sorry
