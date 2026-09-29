-- Prove2me | Theorems.Thm_ProjSpaceCech_GradedModule_Presentation_ker_isFG
-- name    : ProjSpaceCech.GradedModule.Presentation.ker_isFG
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/3fc4965e-b6eb-594e-a5c8-4f007897c0b4
-- title:
--   Kernels of graded presentations are again finitely generated
-- statement:
--   Let $R$ be a commutative Noetherian ring, let $n$ be a natural number, and let $D$ be a [`ProjSpaceCech.GradedModule R n`](def/AlgebraicGeometry_ProjSpaceCechGradedModule.html#L18): an $R$-module $M$ together with a family of $R$-submodules $M_d \subseteq M$ indexed by $d \in \mathbb{Z}$ and $n+1$ pairwise commuting $R$-linear endomorphisms $\mathrm{xMul}_j$ ($j \in \mathrm{Fin}(n+1)$), each carrying $M_d$ into $M_{d+1}$ — so a $\mathbb{Z}$-graded module over $R[x_0,\dots,x_n]$ in this bookkeeping. Let $\sigma$ be a [`ProjSpaceCech.GradedModule.Presentation`](def/AlgebraicGeometry_ProjSpaceCechGradedModule.html#L688) of $D$, that is: a finite index type $J$, a family of degrees $d_0 \colon J \to \mathbb{Z}$, and a homomorphism of graded modules from the product $\prod_{k \in J} \mathrm{FD}\,R\,n\,(d_0\,k)$ of the twisted free graded modules to $D$ which is surjective in each degree, i.e. every element of $D$ lying in grade $d$ is the image of an element of grade $d$ of the source. The conclusion is that the graded module $\sigma.\mathrm{ker}$ — the $\mathrm{xMul}$-stable graded subobject $\sigma.K$ of the source $\sigma.F$, namely the kernel of that homomorphism — itself satisfies `IsFG`: the type of its presentations is nonempty, so there exist a finite index type $J'$, degrees $e \colon J' \to \mathbb{Z}$, and a homomorphism of graded modules from $\prod_{l \in J'} \mathrm{FD}\,R\,n\,(e\,l)$ onto $\sigma.\mathrm{ker}$ which is surjective in every grade.
--
--   This is the graded form of the statement that over a Noetherian base the syzygy module of a finite presentation is again finitely presentable, the induction step on which the finiteness of Čech cohomology of graded modules on projective space rests. It is used in the proofs of [`ProjSpaceCech.GradedModule.finite_cohomology_of_isFG`](thm.html#ProjSpaceCech.GradedModule.finite_cohomology_of_isFG), [`ProjSpaceCech.GradedModule.subsingleton_cohomology_shift_of_isFG`](thm.html#ProjSpaceCech.GradedModule.subsingleton_cohomology_shift_of_isFG) and [`ProjSpaceCech.GradedModule.exists_forall_H_zero_shift_eq_sec_mk_of_isFG`](thm.html#ProjSpaceCech.GradedModule.exists_forall_H_zero_shift_eq_sec_mk_of_isFG), where a descending induction replaces a module by the kernel of a presentation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ProjSpaceCech_GradedModule_Presentation_ker_isFG.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.Presentation.ker_isFG {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ} {D : ProjSpaceCech.GradedModule R n}
    (σ : ProjSpaceCech.GradedModule.Presentation D) : ProjSpaceCech.GradedModule.IsFG σ.ker := by sorry
