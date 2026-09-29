-- Prove2me | Theorems.Thm_TwoChartCech_Mumford_flat_K0
-- name    : TwoChartCech.Mumford.flat_K0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/f2fe88fb-8faa-5517-a7df-fe0ddec8959d
-- title:
--   Flatness of the Mumford truncation term K⁰
-- statement:
--   Let $R$ be a commutative ring and let $C^0$, $C^1$ be $R$-modules (in possibly different universes) that are both flat over $R$. Let $d \colon C^0 \to C^1$ be an $R$-linear map such that the quotient $C^1/\operatorname{range} d$ is a finite $R$-module. Attached to such a $d$ the project fixes a natural number $\mathrm{rank}\,d$, obtained from a choice of finite generating family of $C^1/\operatorname{range} d$ indexed by $\mathrm{Fin}(\mathrm{rank}\,d)$, together with an $R$-linear map $\mathrm{lift}\,d \colon R^{\mathrm{rank}\,d} \to C^1$ lifting the chosen surjection onto $C^1/\operatorname{range} d$ through the quotient map $C^1 \to C^1/\operatorname{range} d$, using projectivity of the free module $R^{\mathrm{rank}\,d}$. The degree-zero term of the truncation is the submodule $K^0(d) = \mathrm{KerCoprod.K0}\,d\,(\mathrm{lift}\,d)$ of $C^0 \times R^{\mathrm{rank}\,d}$ cut out by the pair $(d, \mathrm{lift}\,d)$; it is the kernel of the map $C^0 \times R^{\mathrm{rank}\,d} \to C^1$, $(c,a) \mapsto d(c) + (\mathrm{lift}\,d)(a)$, which is surjective by construction. The assertion is that this submodule $K^0(d)$, with its induced $R$-module structure, is flat over $R$.
--
--   This is the flatness half of the truncation construction in Mumford's treatment of cohomology and flatness (Abelian Varieties, §5, Lemma 1): a flat two-term complex with finitely generated cokernel at the top is replaced by a complex whose degree-zero term is flat and whose degree-one term is free of finite rank. It is used by the existence statement for the truncation of a flat complex, by the companion projectivity statement for $K^0$, and in the proof that the fibrewise Euler characteristic computed from a two-chart Čech complex is locally constant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwoChartCech_Mumford_flat_K0.lean

import Definitions.Def_AlgebraicGeometry_MumfordTruncation
import Mathlib.RingTheory.Flat.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open scoped TensorProduct

theorem TwoChartCech.Mumford.flat_K0
    {R : Type u} [CommRing R]
    {C0 : Type v} {C1 : Type w} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1]
    (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)] :
    Module.Flat R (TwoChartCech.Mumford.K0 d) := by sorry
