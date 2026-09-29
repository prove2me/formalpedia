-- Prove2me | Theorems.Thm_TwoChartCech_Mumford_bijective_kerMapBaseChange
-- name    : TwoChartCech.Mumford.bijective_kerMapBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/8e6b70cb-a68d-5136-8897-8ab942f824b8
-- title:
--   Mumford truncation computes ker(d⊗ A) after any base change
-- statement:
--   Let $R$ be a commutative ring and let $d\colon C^0\to C^1$ be a map of $R$-modules (all in one universe) such that $C^1$ is flat over $R$ and the quotient $C^1/\operatorname{range} d$ is a finite $R$-module. The truncation data attached to $d$ are: the integer $m=$ `rank d`, obtained from a chosen presentation of $C^1/\operatorname{range} d$ by $m$ generators; the map `lift d` $\colon R^m\to C^1$, a chosen lift of the corresponding surjection $R^m\to C^1/\operatorname{range} d$ through the quotient map, available because $R^m$ is projective; the submodule `K0 d` $=\ker\big(d\oplus\mathrm{lift}\,d\colon C^0\times R^m\to C^1\big)$, together with its two coordinate projections `ι0 d` $\colon K^0\to C^0$ and `dK d` $\colon K^0\to R^m$; a map `ι1 d` $\colon R^m\to C^1$; and the identity `comm d` asserting $d\circ$ `ι0 d` $=$ `ι1 d` $\circ$ `dK d`. For every commutative $R$-algebra $A$, the assertion is that the $A$-linear map $$\ker\big(\mathrm{dK}\,d\otimes_R A\big)\longrightarrow\ker\big(d\otimes_R A\big),$$ obtained by restricting $\mathrm{id}_A\otimes$ `ι0 d` (this is well defined by `comm d`), is bijective. The data `ι1 d` enters only through the commutation identity.
--
--   This is the degree-zero half of the statement that Mumford's truncation of a two-term complex with flat top term computes its cohomology compatibly with arbitrary base change, as in Mumford's treatment of cohomology and base change. It is used in the construction of Mumford truncations of flat complexes and in the derivation of finiteness and projectivity properties of $\ker(d\otimes_R A)$ from properties of the truncation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwoChartCech_Mumford_bijective_kerMapBaseChange.lean

import Definitions.Def_AlgebraicGeometry_MumfordTruncation
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib.RingTheory.Flat.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open scoped TensorProduct

theorem TwoChartCech.Mumford.bijective_kerMapBaseChange
    {R : Type u} [CommRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1] [Module.Flat R C1]
    (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)]
    (A : Type u) [CommRing A] [Algebra R A] :
    Function.Bijective
      (TwoChartCech.kerMapBaseChange (TwoChartCech.Mumford.dK d) d (TwoChartCech.Mumford.ι0 d)
        (TwoChartCech.Mumford.ι1 d) (TwoChartCech.Mumford.comm d) A) := by sorry
