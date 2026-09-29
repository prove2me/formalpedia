-- Prove2me | Theorems.Thm_ProjSpaceCech_GradedModule_nonempty_HEquiv_pi
-- name    : ProjSpaceCech.GradedModule.nonempty_HEquiv_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/680d0ba4-2f7f-5176-879c-eb8659d027f5
-- title:
--   Čech cohomology commutes with finite products of graded modules
-- statement:
--   Let $R$ be a commutative ring, let $n$ be a natural number, and let $\iota$ be a finite type. A [`ProjSpaceCech.GradedModule R n`](def/AlgebraicGeometry_ProjSpaceCechGradedModule.html#L18) consists of an $R$-module $M$ (a type in a fixed universe, with its additive and module structures), a family of $R$-submodules $\mathrm{grade}(d) \subseteq M$ indexed by $d \in \mathbb{Z}$, and $R$-linear operators $\mathrm{xMul}(j) : M \to M$ for $j \in \mathrm{Fin}(n+1)$ that raise degrees, $\mathrm{xMul}(j)(\mathrm{grade}(d)) \subseteq \mathrm{grade}(d+1)$, and commute with one another. Given such a family $D : \iota \to$ [`ProjSpaceCech.GradedModule R n`](def/AlgebraicGeometry_ProjSpaceCechGradedModule.html#L18), the object [`ProjSpaceCech.GradedModule.pi D`](def/AlgebraicGeometry_ProjSpaceCechGradedModule.html#L489) has underlying module $\prod_k (D\,k).M$, degree-$d$ part the submodule of families whose $k$-th entry lies in $(D\,k).\mathrm{grade}(d)$, and operators acting coordinatewise. For a graded module $E$, [`ProjSpaceCech.GradedModule.H E 0`](def/AlgebraicGeometry_ProjSpaceCechGradedModule.html#L399) is the kernel of the differential [`ProjSpaceCech.GradedModule.d E 0`](def/AlgebraicGeometry_ProjSpaceCechGradedModule.html#L386), and [`ProjSpaceCech.GradedModule.H E (i+1)`](def/AlgebraicGeometry_ProjSpaceCechGradedModule.html#L399) is the kernel of the differential in degree $i+1$ modulo the preimage inside it of the range of the differential in degree $i$. The theorem asserts, for every $i \in \mathbb{N}$, that the type of $R$-linear equivalences $$\mathrm{H}^i(\mathrm{pi}\,D) \;\simeq_R\; \prod_{k \in \iota} \mathrm{H}^i(D\,k)$$ is nonempty; no particular such equivalence is named.
--
--   This is the statement that the Čech cohomology of the standard cover of $\mathbb{P}^n_R$, computed from a graded module, commutes with finite products (equivalently finite direct sums) of graded modules, the cochains, cocycles and coboundaries all being formed coordinatewise. It is used when reducing finiteness and vanishing statements for a finite sum of twists $\bigoplus_k S(d_k)$ to the case of a single twist, by [`ProjSpaceCech.GradedModule.finite_cohomology_pi_FD`](thm.html#ProjSpaceCech.GradedModule.finite_cohomology_pi_FD) and [`ProjSpaceCech.GradedModule.subsingleton_cohomology_shift_of_isFG`](thm.html#ProjSpaceCech.GradedModule.subsingleton_cohomology_shift_of_isFG); the conclusion is phrased as the existence of a linear equivalence, which suffices to transport both finiteness and vanishing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ProjSpaceCech_GradedModule_nonempty_HEquiv_pi.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.nonempty_HEquiv_pi {R : Type u} [CommRing R] {n : ℕ} {ι : Type} [Fintype ι] (D : ι → ProjSpaceCech.GradedModule R n) (i : ℕ) :
    Nonempty (ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.pi D) i ≃ₗ[R] (∀ k, ProjSpaceCech.GradedModule.H (D k) i)) := by sorry
