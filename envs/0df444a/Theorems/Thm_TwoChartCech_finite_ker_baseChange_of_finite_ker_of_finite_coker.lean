-- Prove2me | Theorems.Thm_TwoChartCech_finite_ker_baseChange_of_finite_ker_of_finite_coker
-- name    : TwoChartCech.finite_ker_baseChange_of_finite_ker_of_finite_coker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/a86be7e1-adb6-5ef3-8012-630be11ceb88
-- title:
--   Finiteness of ker(d⊗ A) after base change
-- statement:
--   Let $R$ be a commutative Noetherian ring and let $d\colon C_0\to C_1$ be an $R$-linear map of $R$-modules, with $C_1$ flat over $R$, such that the kernel $\ker d$ and the cokernel $C_1/\operatorname{im} d$ are finite (i.e. finitely generated) $R$-modules. Let $A$ be a commutative Noetherian $R$-algebra (all three types in the same universe). The conclusion is that the $A$-module $\ker\bigl(d\otimes_R A\colon A\otimes_R C_0\to A\otimes_R C_1\bigr)$ — in Lean, the kernel of `d.baseChange A` — is a finite $A$-module. No finiteness is assumed of $C_0$ or $C_1$ themselves, only of the two cohomology modules of the two-term complex $C_0\to C_1$, and flatness is assumed of $C_1$ only.
--
--   This is the degree-zero half of Mumford's finiteness criterion for a two-term complex with finitely generated cohomology (Abelian Varieties, §5, Lemma 1; cf. EGA III §7.7), in the form needed for base change of Čech cohomology along a two-chart cover. It is used in the computation of the rank of the kernel of the base-changed Čech differential for a proper, geometrically reduced, connected scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwoChartCech_finite_ker_baseChange_of_finite_ker_of_finite_coker.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open scoped TensorProduct

theorem TwoChartCech.finite_ker_baseChange_of_finite_ker_of_finite_coker
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C1] (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)]
    (A : Type u) [CommRing A] [Algebra R A] [IsNoetherianRing A] :
    Module.Finite A (LinearMap.ker (d.baseChange A)) := by sorry
