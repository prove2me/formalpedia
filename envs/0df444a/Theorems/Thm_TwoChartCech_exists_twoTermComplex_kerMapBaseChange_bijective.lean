-- Prove2me | Theorems.Thm_TwoChartCech_exists_twoTermComplex_kerMapBaseChange_bijective
-- name    : TwoChartCech.exists_twoTermComplex_kerMapBaseChange_bijective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/ea852f95-fd1b-55f7-abe9-25a434d60ece
-- title:
--   A finite free two-term model for ker d after every base change
-- statement:
--   Let $R$ be a commutative Noetherian ring and let $d \colon C^0 \to C^1$ be an $R$-linear map between $R$-modules $C^0, C^1$ (all three types in a single universe) that are flat over $R$, and assume that $\ker d$ and the cokernel $C^1 / \operatorname{range} d$ are finitely generated $R$-modules. The assertion is that there exist a two-term complex $G$ of finite free modules over $R$ — that is, $R$-modules $G.C_0$ and $G.C_1$, each finitely generated and free, together with an $R$-linear map $G.d \colon G.C_0 \to G.C_1$ — and $R$-linear maps $\iota_0 \colon G.C_0 \to C^0$, $\iota_1 \colon G.C_1 \to C^1$ forming a chain map, i.e. satisfying $d \circ \iota_0 = \iota_1 \circ G.d$, with the following property: for every commutative $R$-algebra $A$ (in the same universe), the map $\ker(G.d \otimes_R \mathrm{id}_A) \to \ker(d \otimes_R \mathrm{id}_A)$ obtained by restricting the base-changed map $\iota_0 \otimes_R \mathrm{id}_A$ to these kernels, namely [`TwoChartCech.kerMapBaseChange`](def/AlgebraicGeometry_TwoChartCech.html#L153), is bijective. Only the kernels are matched; no claim is made about the cokernels of $G.d \otimes_R \mathrm{id}_A$ and $d \otimes_R \mathrm{id}_A$.
--
--   This is the global, non-local form of the degree-zero part of the standard cohomology-and-base-change construction of a complex of finite free modules computing $H^0$ universally (Mumford's lemma in the theory of abelian varieties; Hartshorne III.12). It is used in the two-chart Čech description of $H^0$ of a coherent sheaf, where it supplies the finite free model needed to study sections after base change, freeness of the Kähler differential $H^0$, and families of fibre-wise $H^0$'s.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwoChartCech_exists_twoTermComplex_kerMapBaseChange_bijective.lean

import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Noetherian.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open scoped TensorProduct

theorem TwoChartCech.exists_twoTermComplex_kerMapBaseChange_bijective
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1] (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)] :
    ∃ (G : CoherentBaseChange.TwoTermComplex.{u, u} R) (ι0 : G.C0 →ₗ[R] C0) (ι1 : G.C1 →ₗ[R] C1)
      (comm : d ∘ₗ ι0 = ι1 ∘ₗ G.d),
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective (TwoChartCech.kerMapBaseChange G.d d ι0 ι1 comm A) := by sorry
