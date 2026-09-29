-- Prove2me | Theorems.Thm_ProjSpaceCech_GradedModule_Hom_secMap_bijective_of_saturated
-- name    : ProjSpaceCech.GradedModule.Hom.secMap_bijective_of_saturated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/73e384df-6cc6-5db4-b24b-2f27a1fbcb7e
-- title:
--   Saturated injective maps induce isomorphisms on sections
-- statement:
--   Let $R$ be a commutative ring and $n$ a natural number, and let $D_1, D_2$ be objects of [`ProjSpaceCech.GradedModule R n`](def/AlgebraicGeometry_ProjSpaceCechGradedModule.html#L18), i.e. data consisting of an $R$-module $M$, a family of submodules $\mathrm{grade}(d) \subseteq M$ indexed by $d \in \mathbb{Z}$, and commuting $R$-linear operators $\mathrm{xMul}\,j$ for $j \in \mathrm{Fin}(n+1)$ carrying $\mathrm{grade}(d)$ into $\mathrm{grade}(d+1)$ (the formal stand-in for a $\mathbb{Z}$-graded module over $R[x_0,\dots,x_n]$ together with multiplication by the variables). Let $\varphi$ be a morphism in [`ProjSpaceCech.GradedModule.Hom D₁ D₂`](def/AlgebraicGeometry_ProjSpaceCechGradedModule.html#L596), that is, an $R$-linear map $\varphi.\mathrm{toLinearMap}$ sending $D_1.\mathrm{grade}(d)$ into $D_2.\mathrm{grade}(d)$ for every $d$ and commuting with each $\mathrm{xMul}\,j$. Assume: (i) $\varphi.\mathrm{toLinearMap}$ is injective; (ii) saturation: for every index $j$, every $e \in \mathbb{Z}$ and every $m \in D_2.\mathrm{grade}(e)$ there are $k \in \mathbb{N}$ and $m' \in D_1.\mathrm{grade}(e+k)$ with $\varphi(m') = (\mathrm{xMul}\,j)^k m$. Then for every non-empty finite set $I$ of indices, the induced $R$-linear map [`ProjSpaceCech.GradedModule.Hom.secMap φ I`](def/AlgebraicGeometry_ProjSpaceCechGradedModule.html#L627) between the degree-zero localisations $\mathrm{sec}\,D_1\,I$ and $\mathrm{sec}\,D_2\,I$ — the map applying $\varphi$ to the numerator of a fraction and keeping its denominator exponent vector — is bijective.
--
--   This is the standard comparison statement of graded commutative algebra: a degree-preserving injection which becomes surjective after inverting any single variable induces an isomorphism on the sections of the associated sheaves over each non-empty standard open intersection $\bigcap_{j \in I} D_+(x_j)$ of $\mathbb{P}^n_R$. It feeds the corresponding bijectivity statement for the Čech cochain complexes, [`ProjSpaceCech.GradedModule.Hom.cochainMap_bijective_of_saturated`](thm.html#ProjSpaceCech.GradedModule.Hom.cochainMap_bijective_of_saturated).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ProjSpaceCech_GradedModule_Hom_secMap_bijective_of_saturated.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.Hom.secMap_bijective_of_saturated {R : Type u} [CommRing R] {n : ℕ} {D₁ D₂ : ProjSpaceCech.GradedModule R n} (φ : ProjSpaceCech.GradedModule.Hom D₁ D₂)
    (hinj : Function.Injective φ.toLinearMap)
    (hsat : ∀ (j : Fin (n + 1)) (e : ℤ), ∀ m ∈ D₂.grade e,
      ∃ k : ℕ, ∃ m' ∈ D₁.grade (e + k), φ.toLinearMap m' = (D₂.xMul j ^ k) m)
    (I : Finset (Fin (n + 1))) (hI : I.Nonempty) :
    Function.Bijective (ProjSpaceCech.GradedModule.Hom.secMap φ I) := by sorry
