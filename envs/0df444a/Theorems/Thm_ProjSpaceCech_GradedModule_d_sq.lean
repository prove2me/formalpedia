-- Prove2me | Theorems.Thm_ProjSpaceCech_GradedModule_d_sq
-- name    : ProjSpaceCech.GradedModule.d_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/a080b97f-6469-553d-9503-31adec1df18e
-- title:
--   The alternating Čech differential of a graded module squares to zero
-- statement:
--   Let $R$ be a commutative ring and $n$ a natural number, and let $D$ be a term of [`ProjSpaceCech.GradedModule R n`](def/AlgebraicGeometry_ProjSpaceCechGradedModule.html#L18): that is, an $R$-module $M$ together with a family of $R$-submodules $\mathrm{grade}(d) \subseteq M$ indexed by $d \in \mathbb{Z}$ and $R$-linear endomorphisms $\mathrm{xMul}(j)$ of $M$ for $j \in \mathrm{Fin}(n+1)$ which raise degree by one (each $\mathrm{xMul}(j)$ maps $\mathrm{grade}(d)$ into $\mathrm{grade}(d+1)$) and commute pairwise. For $i \in \mathbb{N}$, the $i$-th cochain module `GradedModule.cochain D i` is the product over all strictly monotone $s : \mathrm{Fin}(i+1) \to \mathrm{Fin}(n+1)$ of the section module `GradedModule.sec D (Idx.img n s)` attached to the image of $s$, and the differential `GradedModule.d D i` is the $R$-linear map to `GradedModule.cochain D (i+1)` whose component at $s : \mathrm{Fin}(i+2) \to \mathrm{Fin}(n+1)$ is $\sum_{j : \mathrm{Fin}(i+2)} (-1)^{j} \cdot \mathrm{faceRes}(s,j)$ applied to the coordinate at the $j$-th face $s \circ \mathrm{succAbove}_j$, where $\mathrm{faceRes}(s,j)$ is the inclusion map `GradedModule.secIncl` along the containment of the image of the $j$-th face in the image of $s$. The assertion is that for every $i$ the composite of `GradedModule.d D i` followed by `GradedModule.d D (i+1)` is the zero linear map from `GradedModule.cochain D i` to `GradedModule.cochain D (i+2)`.
--
--   This is the cochain-complex condition for the alternating Čech complex of a graded module over $R[x_0,\dots,x_n]$ relative to the standard cover of $\mathbb{P}^n_R$ by the loci where a variable is invertible. It is used by the consumers that treat the cochain modules as a genuine complex, namely the long-exact-sequence and finiteness arguments [`ProjSpaceCech.GradedModule.Presentation.finite_H_of_ses`](thm.html#ProjSpaceCech.GradedModule.Presentation.finite_H_of_ses), [`ProjSpaceCech.GradedModule.Presentation.subsingleton_H_of_ses`](thm.html#ProjSpaceCech.GradedModule.Presentation.subsingleton_H_of_ses) and [`ProjSpaceCech.GradedModule.Presentation.forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one`](thm.html#ProjSpaceCech.GradedModule.Presentation.forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ProjSpaceCech_GradedModule_d_sq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.d_sq {R : Type u} [CommRing R] {n : ℕ} (D : ProjSpaceCech.GradedModule R n) (i : ℕ) :
    ProjSpaceCech.GradedModule.d D (i + 1) ∘ₗ ProjSpaceCech.GradedModule.d D i = 0 := by sorry
