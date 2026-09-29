-- Prove2me | Theorems.Thm_ProjSpaceCech_GradedModule_Hom_HMap_bijective_of_saturated
-- name    : ProjSpaceCech.GradedModule.Hom.HMap_bijective_of_saturated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/9446b164-4243-5096-b07c-509a6df84a15
-- title:
--   Saturated injective maps induce isomorphisms on Čech cohomology
-- statement:
--   Fix a commutative ring $R$ and $n : \mathbb{N}$, and let $D_1, D_2$ be objects of [`ProjSpaceCech.GradedModule R n`](def/AlgebraicGeometry_ProjSpaceCechGradedModule.html#L18): each consists of an $R$-module $M$, a family of $R$-submodules $\mathrm{grade}(d) \subseteq M$ indexed by $d \in \mathbb{Z}$, and $R$-linear operators $\mathrm{xMul}(j) : M \to M$ for $j \in \mathrm{Fin}(n+1)$ that pairwise commute and raise degrees, $\mathrm{xMul}(j)(\mathrm{grade}(d)) \subseteq \mathrm{grade}(d+1)$. Let $\varphi$ be a morphism `GradedModule.Hom D₁ D₂`, i.e. an $R$-linear map $\varphi =$ `φ.toLinearMap` from $D_1.M$ to $D_2.M$ carrying $D_1.\mathrm{grade}(d)$ into $D_2.\mathrm{grade}(d)$ for every $d$ and commuting with each $\mathrm{xMul}(j)$. Assume (hinj) that $\varphi$ is injective on all of $D_1.M$, and (hsat) that for every $j \in \mathrm{Fin}(n+1)$, every $e \in \mathbb{Z}$ and every $m \in D_2.\mathrm{grade}(e)$ there are $k \in \mathbb{N}$ and $m' \in D_1.\mathrm{grade}(e+k)$ with $\varphi(m') = \mathrm{xMul}(j)^k(m)$. Then for every $i : \mathbb{N}$ the induced $R$-linear map `GradedModule.Hom.HMap φ i` on the $i$-th cohomology of the Čech complexes of $D_1$ and $D_2$ is bijective; `HMap φ i` is, for $i = 0$, the restriction of the cochain map `cochainMap φ 0` to the kernels of the differentials, and, for $i = j+1$, the map induced by `cochainMapKer φ (j+1)` on the quotient of the kernel of the differential by the image of the previous one.
--
--   This is the statement that the Čech cohomology of the sheaf attached to a graded module over $R[x_0,\dots,x_n]$ depends only on the localisations at the coordinates: an injective morphism which becomes surjective after inverting any single $x_j$ (the saturation hypothesis hsat) induces isomorphisms on all Čech cohomology groups of $\mathbb{P}^n_R$. It is used to replace a graded module by a more convenient model agreeing with it in large degrees, in the results [`AlgebraicGeometry.ProjSpace.exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion`](thm.html#AlgebraicGeometry.ProjSpace.exists_forall_mem_grade_exists_isHomogeneous_forall_apply_eq_of_isClosedImmersion) and [`AlgebraicGeometry.ProjSpace.exists_forall_subsingleton_HSucc_twist`](thm.html#AlgebraicGeometry.ProjSpace.exists_forall_subsingleton_HSucc_twist).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ProjSpaceCech_GradedModule_Hom_HMap_bijective_of_saturated.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.Hom.HMap_bijective_of_saturated {R : Type u} [CommRing R] {n : ℕ} {D₁ D₂ : ProjSpaceCech.GradedModule R n} (φ : ProjSpaceCech.GradedModule.Hom D₁ D₂)
    (hinj : Function.Injective φ.toLinearMap)
    (hsat : ∀ (j : Fin (n + 1)) (e : ℤ), ∀ m ∈ D₂.grade e,
      ∃ k : ℕ, ∃ m' ∈ D₁.grade (e + k), φ.toLinearMap m' = (D₂.xMul j ^ k) m) (i : ℕ) :
    Function.Bijective (ProjSpaceCech.GradedModule.Hom.HMap φ i) := by sorry
