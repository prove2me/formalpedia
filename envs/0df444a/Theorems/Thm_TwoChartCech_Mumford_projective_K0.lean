-- Prove2me | Theorems.Thm_TwoChartCech_Mumford_projective_K0
-- name    : TwoChartCech.Mumford.projective_K0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/83b7c529-8159-539a-82c2-8238436c70a5
-- title:
--   Projectivity of Mumford's truncation term K⁰
-- statement:
--   Let $R$ be a commutative Noetherian ring and let $C^0$, $C^1$ be $R$-modules (in arbitrary universes) that are flat over $R$, and let $d \colon C^0 \to C^1$ be an $R$-linear map such that both $\ker d$ and $C^1/\operatorname{im} d$ are finite (finitely generated) $R$-modules. The finiteness of the cokernel supplies, through [`TwoChartCech.Mumford.rank`](def/AlgebraicGeometry_MumfordTruncation.html#L54), a natural number $n = \mathrm{rank}\, d$ together with a surjection $R^{n} = (\mathrm{Fin}\, n \to R) \twoheadrightarrow C^1/\operatorname{im} d$ chosen from the finiteness witness, and [`TwoChartCech.Mumford.lift`](def/AlgebraicGeometry_MumfordTruncation.html#L62) is a chosen lifting of that surjection through the quotient map $C^1 \to C^1/\operatorname{im} d$, i.e. an $R$-linear map $\mathrm{lift}\, d \colon R^{n} \to C^1$; the module in question is $K^0 =$ [`TwoChartCech.Mumford.K0 d`](def/AlgebraicGeometry_MumfordTruncation.html#L81), by definition the submodule `KerCoprod.K0 d (lift d)` of $C^0 \times R^{n}$ attached to the pair of maps $d$ and $\mathrm{lift}\, d$ into $C^1$. The assertion is that this $R$-module $K^0$ is projective.
--
--   This is the projectivity half of Mumford's truncation lemma (Abelian Varieties, §5, Lemma 1) for a two-term complex of flat modules with finitely generated cohomology over a Noetherian base: the replacement complex $K^0 \to R^{n}$ has projective terms. It is used in the construction of the truncated complex, in particular by [`TwoChartCech.Mumford.projective_ker_of_fibre_surjective`](thm.html#TwoChartCech.Mumford.projective_ker_of_fibre_surjective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwoChartCech_Mumford_projective_K0.lean

import Definitions.Def_AlgebraicGeometry_MumfordTruncation
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.Projective

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open scoped TensorProduct

theorem TwoChartCech.Mumford.projective_K0
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 : Type v} {C1 : Type w} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1]
    (d : C0 →ₗ[R] C1) [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)] :
    Module.Projective R (TwoChartCech.Mumford.K0 d) := by sorry
