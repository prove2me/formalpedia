-- Prove2me | Theorems.Thm_TwoChartCech_isClosed_setOf_le_finrank_ker_baseChange
-- name    : TwoChartCech.isClosed_setOf_le_finrank_ker_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/ad88c38f-fcc2-5831-81e2-00be8936900e
-- title:
--   Upper semicontinuity of ker dimension for a two-term complex
-- statement:
--   Let $R$ be a Noetherian commutative ring and let $d \colon C^0 \to C^1$ be an $R$-linear map between $R$-modules $C^0, C^1$ that are flat over $R$, and assume that $\ker d$ and the cokernel $C^1 / \operatorname{im} d$ are finitely generated over $R$. Let $T$ be a scheme and $f \colon T \to \operatorname{Spec} R$ a morphism of schemes, and let $n$ be a natural number. For a point $x$ of $T$ write $\kappa(f(x))$ for the residue field of the prime ideal of $R$ corresponding to the image point $f(x)$, and let $d \otimes_R \kappa(f(x))$ be the base change of $d$ along $R \to \kappa(f(x))$. The assertion is that the subset of $T$ consisting of those $x$ for which $n \le \dim_{\kappa(f(x))} \ker\bigl(d \otimes_R \kappa(f(x))\bigr)$ is closed in $T$; equivalently, the function sending $x$ to the dimension of the kernel of the fibre of $d$ at $f(x)$ is upper semicontinuous on $T$.
--
--   This is the degree-zero case of the semicontinuity theorem, formulated for an arbitrary two-term complex of flat modules with finitely generated kernel and cokernel and for an arbitrary scheme mapping to the base. It is used in the relative Picard constructions of the project, where such a complex arises as the Čech differential of a two-chart cover, to obtain closedness of loci where the fibrewise space of sections is large, in particular of the locus where a fibre module is isomorphic to the unit.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwoChartCech_isClosed_setOf_le_finrank_ker_baseChange.lean

import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

theorem TwoChartCech.isClosed_setOf_le_finrank_ker_baseChange
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1] (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)]
    {T : Scheme.{u}} (f : T ⟶ Spec (.of R)) (n : ℕ) :
    IsClosed {x : T | n ≤ Module.finrank (f.base x).asIdeal.ResidueField
      (LinearMap.ker (d.baseChange (f.base x).asIdeal.ResidueField))} := by sorry
