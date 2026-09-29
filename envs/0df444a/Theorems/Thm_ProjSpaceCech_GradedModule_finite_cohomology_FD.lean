-- Prove2me | Theorems.Thm_ProjSpaceCech_GradedModule_finite_cohomology_FD
-- name    : ProjSpaceCech.GradedModule.finite_cohomology_FD
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/94954d83-9f6d-542d-a562-391e928bd507
-- title:
--   Finiteness of Hⁱ(Pⁿ_R,S(d₀)̃)
-- statement:
--   Fix a commutative ring $R$ (in a universe $u$), a natural number $n$, an integer $d_0$ and a natural number $i$. Let `GradedModule.free R n` be the graded module whose underlying $R$-module is $S = R[x_0,\dots,x_n] =$ `MvPolynomial (Fin (n+1)) R`, whose degree-$d$ piece is the submodule of homogeneous polynomials of degree $d$ for $d \ge 0$ and the zero submodule for $d < 0$, and whose commuting operators $x_j\cdot(-)$ are multiplication by the variables $X_j$; let `GradedModule.FD R n d₀` be its shift by $d_0$, i.e. the same $R$-module and the same multiplication operators with grading $d \mapsto S_{d+d_0}$, so the twist $S(d_0)$. Let `GradedModule.H` denote the cohomology of the project's Čech-type complex attached to a graded module, defined recursively as $\ker(\mathrm{d}^0)$ in degree $0$ and, in degree $i+1$, as $\ker(\mathrm{d}^{i+1})$ modulo the preimage of $\operatorname{im}(\mathrm{d}^{i})$ under the inclusion of $\ker(\mathrm{d}^{i+1})$. The assertion is that $H^i$ of $S(d_0)$ in this model is a finite, i.e. finitely generated, $R$-module. No Noetherian or finiteness hypothesis on $R$ is imposed.
--
--   This is Serre's finiteness theorem for the coherent sheaves $\mathcal{O}_{\mathbb{P}^n_R}(d_0)$, in the graded-module presentation of the Čech complex on the standard cover $\{D_+(x_j)\}$. It serves as the base case from which finiteness of Čech cohomology for finitely generated graded modules is obtained, and is used directly for finite products of twists.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ProjSpaceCech_GradedModule_finite_cohomology_FD.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.finite_cohomology_FD (R : Type u) [CommRing R] (n : ℕ) (d₀ : ℤ) (i : ℕ) :
    Module.Finite R (ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.FD R n d₀) i) := by sorry
