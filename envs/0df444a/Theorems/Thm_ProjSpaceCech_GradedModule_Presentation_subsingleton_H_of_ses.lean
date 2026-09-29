-- Prove2me | Theorems.Thm_ProjSpaceCech_GradedModule_Presentation_subsingleton_H_of_ses
-- name    : ProjSpaceCech.GradedModule.Presentation.subsingleton_H_of_ses
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/806dd7ff-8a64-5b84-99a6-ada4cccf387f
-- title:
--   Dévissage: vanishing of Hⁱ from a presentation
-- statement:
--   Let $R$ be a commutative ring, $n$ a natural number, and $D$ a [`ProjSpaceCech.GradedModule R n`](def/AlgebraicGeometry_ProjSpaceCechGradedModule.html#L18), that is an $R$-module together with a $\mathbb{Z}$-indexed family of submodules `grade` and $n+1$ pairwise commuting $R$-linear operators `xMul j` each raising degree by one. For such a graded module and each $i$, `GradedModule.H D i` denotes the $i$-th cohomology of the associated complex: for $i=0$ the kernel of `d D 0`, and for $i+1$ the quotient of the kernel of `d D (i+1)` by the preimage in it of the range of `d D i`. Let $\sigma$ be a `GradedModule.Presentation` of $D$: a finite index type $J$, degrees $d_0\colon J\to\mathbb{Z}$, a homomorphism `hom` from the product over $k\in J$ of the twisted graded modules `GradedModule.FD R n (d₀ k)` to $D$ whose underlying linear map hits every element of every `D.grade d` from the corresponding graded piece of the source, and let `σ.F` be that product and `σ.ker` the graded module obtained from `σ.F` by restricting to the `xMul`-stable family `σ.K` via `GradedModule.sub`. Let $i$ be a natural number. If `GradedModule.H σ.F i` and `GradedModule.H σ.ker (i + 1)` are subsingletons, then so is `GradedModule.H D i`; for these quotients of modules, being a subsingleton is vanishing.
--
--   This is the dévissage step in the proof of Serre's vanishing theorem on $\mathbb{P}^n_R$: exactness of $H^i(F)\to H^i(D)\to H^{i+1}(K)$ for the short exact sequence of graded modules attached to a finite presentation by twists, with no Noetherian hypothesis on $R$. It is used by [`ProjSpaceCech.GradedModule.subsingleton_cohomology_shift_of_isFG`](thm.html#ProjSpaceCech.GradedModule.subsingleton_cohomology_shift_of_isFG), where vanishing for finitely generated graded modules is obtained by induction from the case of twists of the free module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ProjSpaceCech_GradedModule_Presentation_subsingleton_H_of_ses.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.Presentation.subsingleton_H_of_ses {R : Type u} [CommRing R] {n : ℕ} {D : ProjSpaceCech.GradedModule R n}
    (σ : ProjSpaceCech.GradedModule.Presentation D) (i : ℕ)
    (hF : Subsingleton (ProjSpaceCech.GradedModule.H σ.F i)) (hK : Subsingleton (ProjSpaceCech.GradedModule.H σ.ker (i + 1))) :
    Subsingleton (ProjSpaceCech.GradedModule.H D i) := by sorry
