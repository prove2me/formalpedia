-- Prove2me | Theorems.Thm_ProjSpaceCech_GradedModule_Presentation_finite_H_of_ses
-- name    : ProjSpaceCech.GradedModule.Presentation.finite_H_of_ses
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/a828a112-7803-5c8d-a54a-90237a311d3e
-- title:
--   Dévissage step for finiteness of Čech cohomology
-- statement:
--   Let $R$ be a commutative Noetherian ring and $n$ a natural number, and let $D$ be an object of [`ProjSpaceCech.GradedModule R n`](def/AlgebraicGeometry_ProjSpaceCechGradedModule.html#L18): an $R$-module with a family of $R$-submodules `grade d` indexed by $d \in \mathbb{Z}$ together with $R$-linear operators `xMul j`, $j \in \mathrm{Fin}(n+1)$, that carry `grade d` into `grade (d+1)` and commute with one another. For such a $D$ and each $i$, `H D i` denotes the $i$-th cohomology of the associated alternating Čech complex, namely $\ker(\mathrm{d}\,D\,0)$ for $i = 0$ and, for $i+1$, the quotient of $\ker(\mathrm{d}\,D\,(i+1))$ by the pullback along its inclusion of the range of $\mathrm{d}\,D\,i$. Let $\sigma$ be a presentation of $D$: a finite index type $J$, degrees $d_0 : J \to \mathbb{Z}$, and a morphism from the product $\prod_{k \in J} \mathrm{FD}\,R\,n\,(d_0 k)$ of twisted free graded modules to $D$ which is surjective in each degree; write $\sigma.F$ for its source and $\sigma.\mathrm{ker}$ for the graded submodule of $\sigma.F$ given by its degreewise kernel. Then for $i : \mathbb{N}$, if `H σ.F i` and `H σ.ker (i+1)` are finitely generated $R$-modules, so is `H D i`.
--
--   This is the dévissage step in the proof that the Čech cohomology of a finitely generated graded module over $R[x_0,\dots,x_n]$ is finitely generated over a Noetherian base: the portion $H^i(\widetilde{F}) \to H^i(\widetilde{D}) \to H^{i+1}(\widetilde{K})$ of the long exact sequence attached to $0 \to K \to F \to D \to 0$, in the form needed to propagate finiteness. It is used by [`ProjSpaceCech.GradedModule.finite_cohomology_of_isFG`](thm.html#ProjSpaceCech.GradedModule.finite_cohomology_of_isFG).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ProjSpaceCech_GradedModule_Presentation_finite_H_of_ses.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.Presentation.finite_H_of_ses {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ} {D : ProjSpaceCech.GradedModule R n}
    (σ : ProjSpaceCech.GradedModule.Presentation D) (i : ℕ)
    (hF : Module.Finite R (ProjSpaceCech.GradedModule.H σ.F i)) (hK : Module.Finite R (ProjSpaceCech.GradedModule.H σ.ker (i + 1))) :
    Module.Finite R (ProjSpaceCech.GradedModule.H D i) := by sorry
