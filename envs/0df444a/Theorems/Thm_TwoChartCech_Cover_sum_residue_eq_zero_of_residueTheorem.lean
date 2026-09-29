-- Prove2me | Theorems.Thm_TwoChartCech_Cover_sum_residue_eq_zero_of_residueTheorem
-- name    : TwoChartCech.Cover.sum_residue_eq_zero_of_residueTheorem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/ad2b48cd-4721-506b-b2af-b8a9679f0e2c
-- title:
--   Vanishing of chart residue sums from the residue theorem
-- statement:
--   Let $k$ be a field and $F$ a field extension of $k$ equipped with canonical local residue data at every place (in the starred form, whose residue kills the monomials $\pi_v^{-(n+1)}$ for $n\ge 1$), such that at each place $v$ of $F/k$ the element $v.\mathrm{dCoord}$ spans over $F$, such that $\Omega_{F/k}$ is nontrivial, and such that every nonzero differential, respectively every nonzero element of $F$, has an associated divisor (the latter of degree $0$). Assume the residue theorem [`AlgebraicCurve.ResidueTheorem k F`](def/AlgebraicCurve_WeilOfKaehler.html#L107): for every nonzero $\omega\in\Omega_{F/k}$ and every $f\in F$, the Weil functional attached to $\omega$ vanishes on the diagonal adele of $f$. Let $\mathcal U$ be a two-chart cover of $k$, with overlap algebra $\mathcal U.A_{01}$, let $\iota$ be a finite index type, $\Lambda\colon\iota\to\mathcal U.\mathrm{LaurentChart}$ a family of Laurent expansions $\mathcal U.A_{01}\to k(\!(t)\!)$ (each a ring homomorphism restricting to constants on $k$), with residue functionals $\mathrm{Res}_{\Lambda_i}\colon\Omega_{\mathcal U.A_{01}/k}\to k$ given by the coefficient of $t^{-1}$ of the induced expansion of a differential, let $\Phi\colon\Omega_{\mathcal U.A_{01}/k}\to\Omega_{F/k}$ be $k$-linear and $p\colon\iota\hookrightarrow$ places of $F/k$ an injection. Suppose for all $i$ and all $\eta$ that $\mathrm{Res}_{\Lambda_i}(\eta)$ equals the Kähler residue term of $\Phi\eta$ at $p(i)$ against the constant family $1$, that is the trace to $k$ of the residue field of $p(i)$ of the local residue of $1\cdot$ the differential coefficient of $\Phi\eta$. Then for any $\eta\in\Omega_{\mathcal U.A_{01}/k}$ whose image $\Phi\eta$ has vanishing Kähler residue term (again against the constant family $1$) at every place outside the image of $p$, one has $\sum_{i\in\iota}\mathrm{Res}_{\Lambda_i}(\eta)=0$.
--
--   This is the residue theorem for a function field repackaged for the two-chart Čech description of $H^1$: the sum of local Laurent-chart residues of a class vanishes once those residues are identified with canonical residue terms at distinct places and the global differential is regular elsewhere. It feeds the verification of the residue-vanishing condition on coboundaries used in the construction of the Čech Serre pairing, being cited by [`AlgebraicGeometry.Scheme.TwoAffineOpenCover.residuesVanishOnCoboundaries_of_isSectional_of_isCompletionAlong_of_hasParameter`](thm.html#AlgebraicGeometry.Scheme.TwoAffineOpenCover.residuesVanishOnCoboundaries_of_isSectional_of_isCompletionAlong_of_hasParameter).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwoChartCech_Cover_sum_residue_eq_zero_of_residueTheorem.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechLaurentChart
import Definitions.Def_AlgebraicCurve_WeilOfKaehler

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u w

theorem TwoChartCech.Cover.sum_residue_eq_zero_of_residueTheorem
    {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar k F]
    [∀ v : AlgebraicCurve.Place k F, v.DCoordGenerates] [Nontrivial Ω[F⁄k]]
    [AlgebraicCurve.HasCanonicalDivisor (K := k) (F := F)] [AlgebraicCurve.HasPrincipalDivisors k F]
    (hRT : AlgebraicCurve.ResidueTheorem k F)
    (𝒰 : TwoChartCech.Cover.{u, u} k) {ι : Type w} [Fintype ι] (Λ : ι → 𝒰.LaurentChart)
    (Φ : Ω[𝒰.A01⁄k] →ₗ[k] Ω[F⁄k]) (p : ι ↪ AlgebraicCurve.Place k F)
    (hres : ∀ (i : ι) (η : Ω[𝒰.A01⁄k]),
      (Λ i).residue η = AlgebraicCurve.kaehlerResidueTerm (Φ η) (AlgebraicCurve.diagonalHom k F 1) (p i))
    (η : Ω[𝒰.A01⁄k])
    (hreg : ∀ v : AlgebraicCurve.Place k F, v ∉ Set.range p →
      AlgebraicCurve.kaehlerResidueTerm (Φ η) (AlgebraicCurve.diagonalHom k F 1) v = 0) :
    ∑ i, (Λ i).residue η = 0 := by sorry
