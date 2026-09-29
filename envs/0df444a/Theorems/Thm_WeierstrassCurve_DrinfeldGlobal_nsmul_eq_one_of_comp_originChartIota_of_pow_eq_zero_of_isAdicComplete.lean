-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_of_comp_originChartIota_of_pow_eq_zero_of_isAdicComplete
-- name    : WeierstrassCurve.DrinfeldGlobal.nsmul_eq_one_of_comp_originChartIota_of_pow_eq_zero_of_isAdicComplete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/a58ceda1-d049-523b-9635-ab8f3bbda1ed
-- title:
--   Multiplication by q kills nilpotent origin-chart points in characteristic q
-- statement:
--   Let $A$ be a commutative ring and let $\mathcal{G}$ be a family of group laws over $A$, i.e. an assignment to every commutative $A$-algebra $T$, every projective Weierstrass curve $W$ over $T$ and every witness that $\Delta(W)$ is a unit of a relative group law on the structure morphism $\mathrm{Proj}$ of the graded model ring of $W$ over $\mathrm{Spec}\,T$. Assume $\mathcal{G}$ is chord-and-tangent, that is, each member admits a points-evaluation datum, and that it has origin identity: for each member there is a ring homomorphism $\chi$ from the origin chart ring $D_+(Y)$ to $T$ which is an origin-chart section of the identity section and sends $X/Y$ and $Z/Y$ to $0$. Let $q$ be prime, let $T$ be an $A$-algebra of characteristic $q$, and let $W$ be a Weierstrass curve over $T$ with $\Delta(W)$ a unit. Let $R$ be a Noetherian local ring, complete for its maximal-ideal adic topology, let $\rho : T \to R$ be a ring homomorphism, and let $x$ be a morphism $\mathrm{Spec}\,R \to \mathrm{Proj}$ whose composite with the structure morphism is $\mathrm{Spec}\,\rho$. Suppose $x$ factors as $\mathrm{Spec}\,\chi$ followed by the origin chart immersion $\mathrm{originCharti}$, for a ring homomorphism $\chi$ from the origin chart ring of $W$ to $R$ with $\chi(X/Y)^q = 0$ and $\chi(Z/Y)^q = 0$. Then the $q$-fold iterate of $x$ under the group law $\mathcal{G}\,T\,W$ equals its identity section over $\mathrm{Spec}\,\rho$.
--
--   This is the chart-level form of the statement that multiplication by $q$ annihilates the kernel of the relative Frobenius in characteristic $q$: a point of the Weierstrass model lying in the origin chart whose two affine parameters are killed by the $q$-th power is $q$-torsion for the given group law. It feeds the Artinian-local case [`WeierstrassCurve.DrinfeldGlobal.nsmul_eq_one_of_comp_eq_one_of_zChart_pow_originChart_pow_of_isArtinianRing`](thm.html#WeierstrassCurve.DrinfeldGlobal.nsmul_eq_one_of_comp_eq_one_of_zChart_pow_originChart_pow_of_isArtinianRing), used in the analysis of level-$p$ structures on Weierstrass curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_of_comp_originChartIota_of_pow_eq_zero_of_isAdicComplete.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.nsmul_eq_one_of_comp_originChartIota_of_pow_eq_zero_of_isAdicComplete
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (q : ℕ) [Fact q.Prime]
    (T : Type) [CommRing T] [Algebra A T] [CharP T q]
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (ρ : T →+* R)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (projModelStrCR W.toProjective))
    (χ : OriginChartRing W.toProjective →+* R)
    (hx : x.1 = Spec.map (CommRingCat.ofHom χ) ≫ originChartι W.toProjective)
    (hX : (χ (xOverY W.toProjective)) ^ q = 0) (hZ : (χ (zOverY W.toProjective)) ^ q = 0) :
    (𝒢 T W hΔ).nsmul _ q x = (𝒢 T W hΔ).one _ := by sorry
