-- Prove2me | Theorems.Thm_TwoChartCech_Mumford_projective_ker_of_fibre_surjective
-- name    : TwoChartCech.Mumford.projective_ker_of_fibre_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/dd77780e-f2e8-593f-9168-caaf8cd43040
-- title:
--   Cohomology and base change in degree 0 over a Noetherian base
-- statement:
--   Let $A$ be a Noetherian commutative ring and let $C^0$, $C^1$ be $A$-modules (in the same universe as $A$) which are flat over $A$, and let $d\colon C^0\to C^1$ be an $A$-linear map such that $\ker d$ and the cokernel $C^1/\operatorname{im} d$ are finitely generated $A$-modules. Assume that for every field $K$ equipped with an $A$-algebra structure the base-changed map $d\otimes_A K\colon K\otimes_A C^0\to K\otimes_A C^1$ is surjective. Then three things hold simultaneously: (i) $\ker d$ is a projective $A$-module; (ii) for every commutative $A$-algebra $A'$ (again in the same universe) the canonical $A'$-linear map $A'\otimes_A\ker d\to\ker(d\otimes_A A')$, namely the one induced by the inclusion $\ker d\hookrightarrow C^0$ after base change and corestricted to the kernel of $d\otimes_A A'$, is bijective; and (iii) for every field $K$ with an $A$-algebra structure one has $\dim_K\bigl(K\otimes_A\ker d\bigr)=\dim_K\ker\bigl(d\otimes_A K\bigr)$.
--
--   This is the degree-zero cohomology-and-base-change theorem for a two-term flat complex, in the form used to deduce that the $0$-th cohomology of such a complex with everywhere-surjective differential on fibres is locally free of constant rank and commutes with arbitrary base change. It is applied in the scheme-theoretic statements about base change of modules along affine morphisms and over two-chart affine open covers, and to local freeness of pushforwards.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwoChartCech_Mumford_projective_ker_of_fibre_surjective.lean

import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open scoped TensorProduct

theorem TwoChartCech.Mumford.projective_ker_of_fibre_surjective
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {C0 C1 : Type u} [AddCommGroup C0] [Module A C0] [AddCommGroup C1] [Module A C1]
    [Module.Flat A C0] [Module.Flat A C1] (d : C0 →ₗ[A] C1)
    [Module.Finite A (LinearMap.ker d)] [Module.Finite A (C1 ⧸ LinearMap.range d)]
    (hH1 : ∀ (K : Type u) [Field K] [Algebra A K], Function.Surjective (d.baseChange K)) :
    Module.Projective A (LinearMap.ker d) ∧
      (∀ (A' : Type u) [CommRing A'] [Algebra A A'], Function.Bijective (TwoChartCech.kerBaseChangeHom d A')) ∧
      ∀ (K : Type u) [Field K] [Algebra A K],
        Module.finrank K (K ⊗[A] LinearMap.ker d) = Module.finrank K (LinearMap.ker (d.baseChange K)) := by sorry
