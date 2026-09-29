-- Prove2me | Theorems.Thm_ProjSpaceCech_GradedModule_finite_cohomology_pi_FD
-- name    : ProjSpaceCech.GradedModule.finite_cohomology_pi_FD
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/285deda5-0141-5717-95c1-42015acb5a6d
-- title:
--   Finiteness of Čech cohomology of a finite sum of twists
-- statement:
--   Let $R$ be a commutative ring, $n$ a natural number, $\iota$ a finite index type, $(d_0(k))_{k\in\iota}$ a family of integers, and $i$ a natural number. For each $k$, [`ProjSpaceCech.GradedModule.FD R n (d₀ k)`](def/AlgebraicGeometry_ProjSpaceCechGradedModule.html#L559) is the graded module obtained from the free one — the polynomial ring $R[x_0,\dots,x_n]$ with its grading by homogeneous components (negative degrees given the zero submodule) and with the operators given by multiplication by the variables $x_j$ — by shifting the grading, so that the degree-$d$ part is the degree-$(d+d_0(k))$ part of the polynomial ring. Their product [`ProjSpaceCech.GradedModule.pi`](def/AlgebraicGeometry_ProjSpaceCechGradedModule.html#L489) has underlying module $\prod_{k\in\iota}R[x_0,\dots,x_n]$, degree-$d$ part the tuples whose $k$-th entry lies in the degree-$d$ part of the $k$-th factor, and componentwise multiplication operators. For a graded module $D$, [`ProjSpaceCech.GradedModule.H D i`](def/AlgebraicGeometry_ProjSpaceCechGradedModule.html#L399) is the $i$-th cohomology of the associated Čech-type complex: the kernel of $d^0$ when $i=0$, and otherwise the kernel of $d^{i}$ modulo the preimage in it of the image of $d^{i-1}$. The assertion is that $H^i$ of this product of shifted free graded modules is a finitely generated $R$-module. No Noetherian hypothesis is imposed on $R$.
--
--   This is the case of a finite direct sum of twisting sheaves in Serre's finiteness theorem for coherent cohomology on $\mathbb{P}^n_R$, in the graded-module Čech model: $H^i(\mathbb{P}^n_R,\bigoplus_{k}\mathcal{O}(d_k))$ is a finitely generated $R$-module. It serves as the base case of the dévissage in [`ProjSpaceCech.GradedModule.finite_cohomology_of_isFG`](thm.html#ProjSpaceCech.GradedModule.finite_cohomology_of_isFG), which treats finitely generated graded modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ProjSpaceCech_GradedModule_finite_cohomology_pi_FD.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.finite_cohomology_pi_FD (R : Type u) [CommRing R] (n : ℕ) {ι : Type} [Fintype ι] (d₀ : ι → ℤ) (i : ℕ) :
    Module.Finite R (ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.pi (fun k => ProjSpaceCech.GradedModule.FD R n (d₀ k))) i) := by sorry
