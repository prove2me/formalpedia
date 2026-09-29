-- Prove2me | Theorems.Thm_Rep_isZero_tateCohomology_res_indBot
-- name    : Rep.isZero_tateCohomology_res_indBot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/14ce9c6e-2ae4-5d96-9e8c-5b5d20ce618c
-- title:
--   Restriction to a finite subgroup of Ind₁^G is Tate-acyclic
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, $S \le G$ a subgroup whose underlying type is finite, $A$ a $k$-linear representation of $G$, and $q$ an integer. Form $A_* =$ `A.indBot`, the representation of $G$ induced along the inclusion $\bot \hookrightarrow G$ from the restriction of $A$ to the trivial subgroup, and restrict it along the inclusion $S \hookrightarrow G$ to obtain a representation of $S$. The assertion is that the $k$-module $(\operatorname{Res}^G_S A_*)\widehat{H}^q$, namely `tateCohomology` of this $S$-representation in degree $q$, is a zero object of `ModuleCat k`. Here Tate cohomology of a representation $B$ of the finite group $S$ is, by definition, group cohomology $H^{q}(S,B)$ for $q \ge 1$, the quotient of the $S$-invariants of $B$ by the range of the norm map `normBar` for $q = 0$, the kernel of that norm map for $q = -1$, and group homology $H_{-q-1}(S,B)$ for $q \le -2$. Finiteness of $S$ is what makes these degrees simultaneously available.
--
--   This is the Tate-acyclicity of a module induced from the trivial subgroup, in the form needed after restriction to a finite subgroup: as an $S$-representation, $k[G] \otimes A$ decomposes along cosets into copies of $k[S] \otimes A$. It is used by [`Rep.nonempty_tateCohomology_res_dimShiftUpObj_iso_res`](thm.html#Rep.nonempty_tateCohomology_res_dimShiftUpObj_iso_res) and [`Rep.nonempty_tateCohomology_res_iso_res_dimShiftDownObj`](thm.html#Rep.nonempty_tateCohomology_res_iso_res_dimShiftDownObj), so that dimension shifting is compatible with restriction to subgroups and hypotheses on Sylow subgroups can be transported between degrees.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_isZero_tateCohomology_res_indBot.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.isZero_tateCohomology_res_indBot {k G : Type u} [CommRing k] [Group G]
    (S : Subgroup G) [Fintype S] (A : Rep.{u} k G) (q : ℤ) :
    CategoryTheory.Limits.IsZero ((Rep.res S.subtype A.indBot).tateCohomology q) := by sorry
