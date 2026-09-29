-- Prove2me | Theorems.Thm_TwoChartCech_exists_fibreH0Family
-- name    : TwoChartCech.exists_fibreH0Family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/f605db7d-c275-5454-969d-c3366075ea30
-- title:
--   Existence of the h⁰-family of a flat two-term complex
-- statement:
--   Let $R$ be a Noetherian commutative ring and let $d\colon C^0\to C^1$ be an $R$-linear map between flat $R$-modules $C^0,C^1$ (all in one universe) whose kernel $\ker d$ and cokernel $C^1/\operatorname{im} d$ are finitely generated $R$-modules; let $T$ be a scheme and $f\colon T\to\operatorname{Spec} R$ a morphism of schemes. The assertion is that there exists a datum $F$ of type [`CoherentBaseChange.FibreH0Family T`](def/AlgebraicGeometry_CoherentBaseChangeFamily.html#L14), that is: for every open $U\subseteq T$ together with a proof that $U$ is affine, a two-term complex $F.G\,U$ over the ring $\Gamma(T,U)$ consisting of two finite free $\Gamma(T,U)$-modules and a $\Gamma(T,U)$-linear map between them; a function $F.h_0\colon T\to\mathbb{N}$; and the compatibility that for every affine open $U$ and every point $t\in U$, $F.h_0(t)$ equals the fibre invariant of $F.G\,U$ at the prime $\mathfrak q$ of $\Gamma(T,U)$ corresponding to $t$, namely the dimension over the residue field $\kappa(\mathfrak q)$ of the kernel of the base change of the differential of $F.G\,U$ to $\kappa(\mathfrak q)$. Moreover this $F$ may be chosen so that for every point $x\in T$ one has $F.h_0(x)=\dim_{\kappa(\mathfrak p)}\ker\bigl(d\otimes_R\kappa(\mathfrak p)\bigr)$, where $\mathfrak p=f(x)$ is the underlying prime of $R$ and $\kappa(\mathfrak p)$ its residue field.
--
--   This packages base change in degree $0$ for an arbitrary two-term complex with flat terms into a single structure attached to a scheme over $R$: a Zariski-local presentation by finite free two-term complexes whose degree-$0$ fibre ranks are computed by the function $x\mapsto\dim_{\kappa(f(x))}\ker(d\otimes\kappa(f(x)))$. It is the input to [`TwoChartCech.isClosed_setOf_le_finrank_ker_baseChange`](thm.html#TwoChartCech.isClosed_setOf_le_finrank_ker_baseChange), where upper semicontinuity of this function on $T$ is deduced; the motivating $d$ is a two-chart Čech differential.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwoChartCech_exists_fibreH0Family.lean

import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicGeometry_CoherentBaseChangeFamily
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

theorem TwoChartCech.exists_fibreH0Family
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1] (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)]
    {T : Scheme.{u}} (f : T ⟶ Spec (.of R)) :
    ∃ F : CoherentBaseChange.FibreH0Family T,
      ∀ x : T, F.h0 x = Module.finrank (f.base x).asIdeal.ResidueField
        (LinearMap.ker (d.baseChange (f.base x).asIdeal.ResidueField)) := by sorry
