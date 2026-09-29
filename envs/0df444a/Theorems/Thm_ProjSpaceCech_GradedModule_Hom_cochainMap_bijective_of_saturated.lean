-- Prove2me | Theorems.Thm_ProjSpaceCech_GradedModule_Hom_cochainMap_bijective_of_saturated
-- name    : ProjSpaceCech.GradedModule.Hom.cochainMap_bijective_of_saturated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/bccc5dfa-de73-5720-b0e4-10420b0f5ae3
-- title:
--   Saturated injective maps induce bijections on Čech cochains
-- statement:
--   Let $R$ be a commutative ring and $n$ a natural number, and let $D_1, D_2$ be objects of [`ProjSpaceCech.GradedModule R n`](def/AlgebraicGeometry_ProjSpaceCechGradedModule.html#L18): each consists of an $R$-module $M$, a family of submodules $\mathrm{grade}(d) \subseteq M$ indexed by $d \in \mathbb{Z}$, and commuting $R$-linear operators $\mathrm{xMul}\,j$ for $j \in \mathrm{Fin}(n+1)$ which carry $\mathrm{grade}(d)$ into $\mathrm{grade}(d+1)$ (a $\mathbb{Z}$-graded module over $R[x_0,\dots,x_n]$ presented by the multiplication operators). Let $\varphi$ be a morphism `GradedModule.Hom D₁ D₂`, that is, an $R$-linear map $\varphi$ on underlying modules which sends $D_1.\mathrm{grade}(d)$ into $D_2.\mathrm{grade}(d)$ for all $d$ and satisfies $\varphi \circ D_1.\mathrm{xMul}\,j = D_2.\mathrm{xMul}\,j \circ \varphi$ for all $j$. Assume $\varphi$ is injective, and saturated in the following sense: for every $j \in \mathrm{Fin}(n+1)$, every $e \in \mathbb{Z}$ and every $m \in D_2.\mathrm{grade}(e)$ there exist $k \in \mathbb{N}$ and $m' \in D_1.\mathrm{grade}(e+k)$ with $\varphi(m') = (D_2.\mathrm{xMul}\,j)^k(m)$. Then for every $i \in \mathbb{N}$ the induced map on $i$-cochains, `GradedModule.Hom.cochainMap φ i`, namely the product over Čech indices $s$ of type `Idx n i` of the maps `Hom.secMap φ (Idx.img n s)` between degree-zero localised sections, is bijective.
--
--   This is the cochain-level form of the statement that an injective graded map which becomes surjective after inverting any single coordinate induces an isomorphism of the alternating Čech complexes of the associated sheaves on $\mathbb{P}^n_R$ for the standard affine cover. It feeds [`ProjSpaceCech.GradedModule.Hom.HMap_bijective_of_saturated`](thm.html#ProjSpaceCech.GradedModule.Hom.HMap_bijective_of_saturated), which transfers the conclusion to Čech cohomology.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ProjSpaceCech_GradedModule_Hom_cochainMap_bijective_of_saturated.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.Hom.cochainMap_bijective_of_saturated {R : Type u} [CommRing R] {n : ℕ} {D₁ D₂ : ProjSpaceCech.GradedModule R n} (φ : ProjSpaceCech.GradedModule.Hom D₁ D₂)
    (hinj : Function.Injective φ.toLinearMap)
    (hsat : ∀ (j : Fin (n + 1)) (e : ℤ), ∀ m ∈ D₂.grade e,
      ∃ k : ℕ, ∃ m' ∈ D₁.grade (e + k), φ.toLinearMap m' = (D₂.xMul j ^ k) m) (i : ℕ) :
    Function.Bijective (ProjSpaceCech.GradedModule.Hom.cochainMap φ i) := by sorry
