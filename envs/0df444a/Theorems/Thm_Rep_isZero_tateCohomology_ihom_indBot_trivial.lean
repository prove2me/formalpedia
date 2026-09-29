-- Prove2me | Theorems.Thm_Rep_isZero_tateCohomology_ihom_indBot_trivial
-- name    : Rep.isZero_tateCohomology_ihom_indBot_trivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/49297318-641c-52f6-b731-86df2f13dc60
-- title:
--   Tate-acyclicity of Hom_k(Ind₁^G M, W)
-- statement:
--   Let $k$ be a commutative ring and $G$ a finite group, let $M$ be a $k$-module, let $W$ be a $k$-linear representation of $G$, and let $q$ be an integer. Form the trivial representation `Rep.trivial k G M` on $M$, apply `indBot`, i.e. induction along the inclusion of the trivial subgroup $\bot \le G$ of the restriction of that representation to $\bot$, and then take the internal hom of the monoidal category $\mathrm{Rep}\, k\, G$ out of this induced object and evaluated at $W$. The assertion is that the Tate cohomology of the resulting representation in degree $q$ is a zero object of `ModuleCat k`. Here Tate cohomology in degree $q$ is, by definition, group cohomology $H^{q}$ for $q \ge 1$, group homology $H_{-q-1}$ for $q \le -2$, the invariants modulo the range of the norm map `normBar` for $q = 0$, and the kernel of `normBar` for $q = -1$; so the conclusion says that each of these modules, for the given $q$, vanishes.
--
--   This is the acyclicity input saying that $\operatorname{Hom}_k(\operatorname{Ind}_1^G M, W)$ with the conjugation action, being coinduced and hence (for finite $G$) induced from the trivial subgroup, has vanishing Tate cohomology in all degrees. It is used to deduce Tate-acyclicity of internal homs out of free representations and out of representations of $p$-group type, via [`Rep.isZero_tateCohomology_ihom_free`](thm.html#Rep.isZero_tateCohomology_ihom_free) and [`Rep.isZero_tateCohomology_ihom_of_isPGroup`](thm.html#Rep.isZero_tateCohomology_ihom_of_isPGroup), and rests on [`Rep.isZero_tateCohomology_indBot`](thm.html#Rep.isZero_tateCohomology_indBot) together with transport of Tate cohomology along an isomorphism of representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_isZero_tateCohomology_ihom_indBot_trivial.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory

theorem Rep.isZero_tateCohomology_ihom_indBot_trivial {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (M : ModuleCat.{u} k) (W : Rep.{u} k G) (q : ℤ) :
    CategoryTheory.Limits.IsZero (((ihom (Rep.trivial k G M).indBot).obj W).tateCohomology q) := by sorry
