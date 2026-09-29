-- Prove2me | Theorems.Thm_TwoChartCech_kerMap_injective_of_H0_eq_zero
-- name    : TwoChartCech.kerMap_injective_of_H0_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/80461c08-f117-532b-b9ad-7038e1570eb2
-- title:
--   Snake fragment: ker d_E=0 makes ker d_S finite
-- statement:
--   Let $R$ be a Noetherian commutative ring and let $K^0,K^1,E^0,E^1,S^0,S^1$ be $R$-modules (all in one universe), equipped with $R$-linear maps $d_K\colon K^0\to K^1$, $d_E\colon E^0\to E^1$, $d_S\colon S^0\to S^1$ together with $i^0\colon K^0\to E^0$, $i^1\colon K^1\to E^1$, $p^0\colon E^0\to S^0$, $p^1\colon E^1\to S^1$. Assume the two squares commute, in the form $d_E\circ i^0=i^1\circ d_K$ and $d_S\circ p^0=p^1\circ d_E$; assume $i^0$ and $i^1$ are injective, $p^0$ and $p^1$ are surjective, and $\operatorname{range} i^0=\ker p^0$, $\operatorname{range} i^1=\ker p^1$, so that the columns are short exact sequences of two-term complexes; assume $\ker d_E=0$; and assume that the quotient $K^1/\operatorname{range} d_K$ is a finite (finitely generated) $R$-module. The conclusion is that $\ker d_S$ is a finite $R$-module.
--
--   This is the fragment of the snake lemma (long exact cohomology sequence) for a short exact sequence of two-term complexes which says that vanishing of $H^0(E)=\ker d_E$ makes the connecting map $H^0(S)=\ker d_S\to H^1(K)=\operatorname{coker} d_K$ injective, combined with the fact that over a Noetherian ring a submodule of a finitely generated module is finitely generated. It supports the finiteness theorem [`TwoChartCech.Sections.finite_H0_of_chartFinite`](thm.html#TwoChartCech.Sections.finite_H0_of_chartFinite) for Čech $H^0$ of data given on two charts, where a sum of negative twists with vanishing $H^0$ is mapped onto the datum and finiteness of $H^1$ of the syzygy datum is used.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwoChartCech_kerMap_injective_of_H0_eq_zero.lean

import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib.RingTheory.Noetherian.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem TwoChartCech.kerMap_injective_of_H0_eq_zero
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {K0 K1 E0 E1 S0 S1 : Type u}
    [AddCommGroup K0] [Module R K0] [AddCommGroup K1] [Module R K1]
    [AddCommGroup E0] [Module R E0] [AddCommGroup E1] [Module R E1]
    [AddCommGroup S0] [Module R S0] [AddCommGroup S1] [Module R S1]
    (dK : K0 →ₗ[R] K1) (dE : E0 →ₗ[R] E1) (dS : S0 →ₗ[R] S1)
    (i0 : K0 →ₗ[R] E0) (i1 : K1 →ₗ[R] E1) (p0 : E0 →ₗ[R] S0) (p1 : E1 →ₗ[R] S1)
    (hi : dE ∘ₗ i0 = i1 ∘ₗ dK) (hp : dS ∘ₗ p0 = p1 ∘ₗ dE)
    (hi0 : Function.Injective i0) (hi1 : Function.Injective i1)
    (hp0 : Function.Surjective p0) (hp1 : Function.Surjective p1)
    (hex0 : LinearMap.range i0 = LinearMap.ker p0) (hex1 : LinearMap.range i1 = LinearMap.ker p1)
    (hE : LinearMap.ker dE = ⊥) [Module.Finite R (K1 ⧸ LinearMap.range dK)] :
    Module.Finite R (LinearMap.ker dS) := by sorry
