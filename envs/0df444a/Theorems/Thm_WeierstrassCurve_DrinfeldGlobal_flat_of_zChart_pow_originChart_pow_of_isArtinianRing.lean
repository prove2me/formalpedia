-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_flat_of_zChart_pow_originChart_pow_of_isArtinianRing
-- name    : WeierstrassCurve.DrinfeldGlobal.flat_of_zChart_pow_originChart_pow_of_isArtinianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/0a982f2d-798a-5e79-8086-279487329212
-- title:
--   Flatness of the relative Frobenius of a Weierstrass model
-- statement:
--   Let $q$ be a prime, let $T$ be a commutative ring of characteristic $q$ (assumed local and Artinian), and let $W$ be a Weierstrass curve over $T$ whose discriminant $\Delta_W$ is a unit. Write $W^{(q)} = W.\mathrm{map}\,(\mathrm{frobenius}\,T\,q)$ for the curve obtained by applying the $q$-power endomorphism of $T$ to the coefficients, and for a Weierstrass curve $V$ over $T$ let $\mathrm{projModelCR}$ be $\operatorname{Proj}$ of the grading induced on the quotient of the polynomial ring in three variables by the homogeneous ideal of the Weierstrass cubic, with structure morphism $\mathrm{projModelStrCR}$ to $\operatorname{Spec} T$. Let $\Phi$ be a morphism from the projective model of $W$ to that of $W^{(q)}$ which is a morphism over $\operatorname{Spec} T$, i.e. $\Phi$ followed by $\mathrm{projModelStrCR}$ of $W^{(q)}$ equals $\mathrm{projModelStrCR}$ of $W$. Assume furthermore that $\Phi$ is given by $q$-th powers on the two standard charts, in the following sense: there is a ring homomorphism $\psi$ from the degree-zero homogeneous localisation of the model of $W^{(q)}$ away from the class of the third coordinate to the corresponding ring for $W$, sending $X/Z$ to $(X/Z)^q$ and $Y/Z$ to $(Y/Z)^q$, such that the chart immersion $\mathrm{zChartι}$ for $W$ followed by $\Phi$ equals $\operatorname{Spec}\psi$ followed by the chart immersion for $W^{(q)}$; and similarly a ring homomorphism on the localisations away from the class of the second coordinate sending $X/Y$ to $(X/Y)^q$ and $Z/Y$ to $(Z/Y)^q$ and compatible with the immersions $\mathrm{originChartι}$. The conclusion is that $\Phi$ is flat.
--
--   This is the flatness of the relative Frobenius morphism of an elliptic Weierstrass model, characterised here by the requirement that it be the $q$-power map in the two standard affine charts. It is used later in the same development, in the normalisation of a Frobenius-type morphism by a Weierstrass variable change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_flat_of_zChart_pow_originChart_pow_of_isArtinianRing.lean

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

theorem WeierstrassCurve.DrinfeldGlobal.flat_of_zChart_pow_originChart_pow_of_isArtinianRing
    (q : ℕ) [Fact q.Prime] (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [CharP T q]
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
    (Φ : projModelCR W.toProjective ⟶ projModelCR (W.map (frobenius T q)).toProjective)
    (hΦ : Φ ≫ projModelStrCR (W.map (frobenius T q)).toProjective = projModelStrCR W.toProjective)
    (hZ : ∃ ψ : ZChartRing (W.map (frobenius T q)).toProjective →+* ZChartRing W.toProjective,
        ψ (xOverZ (W.map (frobenius T q)).toProjective) = xOverZ W.toProjective ^ q ∧
        ψ (yOverZ (W.map (frobenius T q)).toProjective) = yOverZ W.toProjective ^ q ∧
        zChartι W.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ zChartι (W.map (frobenius T q)).toProjective)
    (hY : ∃ ψ : OriginChartRing (W.map (frobenius T q)).toProjective →+* OriginChartRing W.toProjective,
        ψ (xOverY (W.map (frobenius T q)).toProjective) = xOverY W.toProjective ^ q ∧
        ψ (zOverY (W.map (frobenius T q)).toProjective) = zOverY W.toProjective ^ q ∧
        originChartι W.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ originChartι (W.map (frobenius T q)).toProjective) :
    Flat Φ := by sorry
