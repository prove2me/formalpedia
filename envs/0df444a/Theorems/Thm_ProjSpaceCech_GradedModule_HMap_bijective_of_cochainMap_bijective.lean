-- Prove2me | Theorems.Thm_ProjSpaceCech_GradedModule_HMap_bijective_of_cochainMap_bijective
-- name    : ProjSpaceCech.GradedModule.HMap_bijective_of_cochainMap_bijective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/5175d0e7-2ae2-58d4-83aa-e18e470ae313
-- title:
--   Čech cohomology bijective when cochain maps are bijective
-- statement:
--   Let $R$ be a commutative ring, $n$ a natural number, and let $D_1, D_2$ be objects of [`ProjSpaceCech.GradedModule R n`](def/AlgebraicGeometry_ProjSpaceCechGradedModule.html#L18), that is, $R$-modules equipped with a $\mathbb Z$-indexed family of submodules (the grading) together with $n+1$ pairwise commuting $R$-linear operators $xMul_j$ raising the grading index by one. Let $\varphi$ be a morphism `GradedModule.Hom D₁ D₂`, i.e. an $R$-linear map $D_1.M \to D_2.M$ preserving each graded piece and commuting with all the operators $xMul_j$. For each $i$ it induces a map `Hom.cochainMap φ i` on the alternating Čech cochains $\prod_{s : \mathrm{Idx}\,n\,i} \mathrm{sec}(D, \mathrm{Idx.img}\,n\,s)$, given componentwise by the maps `Hom.secMap φ` on sections. Assume `Hom.cochainMap φ i` is bijective for every $i$. Then for every $i$ the induced map `Hom.HMap φ i` on cohomology is bijective; here `Hom.HMap φ 0` is the restriction of the cochain map to $\ker d^0$, and `Hom.HMap φ (j+1)` is the map induced on the quotient of $\ker d^{\,j+1}$ by the image of $d^{\,j}$.
--
--   This is the standard fact that an isomorphism of cochain complexes induces isomorphisms on cohomology, in the concrete setting of the alternating Čech complex of a graded module on the standard cover of $\mathbb P^n_R$. It is used as a transfer tool: it is cited in the proofs that the induced cohomology maps are bijective under a saturation hypothesis and that cohomology of a shifted finitely generated graded module is subsingleton.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ProjSpaceCech_GradedModule_HMap_bijective_of_cochainMap_bijective.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.HMap_bijective_of_cochainMap_bijective {R : Type u} [CommRing R] {n : ℕ} {D₁ D₂ : ProjSpaceCech.GradedModule R n}
    (φ : ProjSpaceCech.GradedModule.Hom D₁ D₂) (h : ∀ i, Function.Bijective (ProjSpaceCech.GradedModule.Hom.cochainMap φ i)) (i : ℕ) :
    Function.Bijective (ProjSpaceCech.GradedModule.Hom.HMap φ i) := by sorry
