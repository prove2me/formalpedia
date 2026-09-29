-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_of_comp_eq_one_of_zChart_pow_originChart_pow_of_isArtinianRing
-- name    : WeierstrassCurve.DrinfeldGlobal.nsmul_eq_one_of_comp_eq_one_of_zChart_pow_originChart_pow_of_isArtinianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/bf2e4b9b-452a-586f-83ac-1e8d5f3c1130
-- title:
--   Frobenius kernel killed by q: Artinian local points
-- statement:
--   Let $A$ be a commutative ring and let $\mathcal G$ be a family of group laws over $A$, i.e. an assignment, to every $A$-algebra $T$ and every projective Weierstrass curve $W$ over $T$ with $\Delta(W)$ a unit, of a relative group law on the structure morphism `projModelStrCR` of the projective model; assume $\mathcal G$ is chord–tangent (each member admits an evaluation `ev` with `IsPointsEval`) and has origin as identity (for each member there is a ring homomorphism $\chi$ from the origin chart ring to $T$ which is an origin-chart section of the unit and kills `xOverY` and `zOverY`). Let $q$ be prime, let $T$ be an Artinian local $A$-algebra of characteristic $q$, let $W$ be a Weierstrass curve over $T$ with $\Delta(W)$ and $\Delta(W^{(q)})$ units, where $W^{(q)}$ is the base change of $W$ along the Frobenius $x \mapsto x^q$ of $T$. Let $\Phi$ be a finite morphism from the projective model of $W$ to that of $W^{(q)}$ over $\operatorname{Spec} T$ (that is, $\Phi$ followed by `projModelStrCR` of $W^{(q)}$ is `projModelStrCR` of $W$), which on the two standard charts is $q$-th power: there are ring homomorphisms $\psi$ of the $Z$-chart rings with $\psi(\mathrm{xOverZ}) = \mathrm{xOverZ}^q$, $\psi(\mathrm{yOverZ}) = \mathrm{yOverZ}^q$ and $\mathrm{zChart}\iota$ of $W$ followed by $\Phi$ equal to $\operatorname{Spec}\psi$ followed by $\mathrm{zChart}\iota$ of $W^{(q)}$, and likewise of the origin chart rings with $\psi(\mathrm{xOverY}) = \mathrm{xOverY}^q$, $\psi(\mathrm{zOverY}) = \mathrm{zOverY}^q$ and the analogous compatibility for $\mathrm{originChart}\iota$. Finally let $B$ be an Artinian local commutative ring, $\rho : T \to B$ a ring homomorphism, and $x$ a morphism from $\operatorname{Spec} B$ to the projective model of $W$ lying over $\operatorname{Spec}\rho$. If the composite of $x$ with $\Phi$, viewed as such a point of the projective model of $W^{(q)}$, is the unit point of the group law $\mathcal G(T, W^{(q)})$, then the $q$-fold iterate `nsmul` of $x$ under $\mathcal G(T, W)$ is the unit point.
--
--   This is the statement that multiplication by $q$ annihilates the kernel of the relative Frobenius on an elliptic curve in characteristic $q$, in the special case of points valued in an Artinian local ring over an Artinian local base. It feeds the corresponding statement for an arbitrary test scheme, [`WeierstrassCurve.DrinfeldGlobal.comp_schemeNsmul_eq_one_of_comp_eq_one_of_zChart_pow_originChart_pow`](thm.html#WeierstrassCurve.DrinfeldGlobal.comp_schemeNsmul_eq_one_of_comp_eq_one_of_zChart_pow_originChart_pow), the general case being reduced to Artinian local points by finiteness of $\Phi$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_of_comp_eq_one_of_zChart_pow_originChart_pow_of_isArtinianRing.lean

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
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel
open WeierstrassCurve.DrinfeldGlobal
attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.nsmul_eq_one_of_comp_eq_one_of_zChart_pow_originChart_pow_of_isArtinianRing
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (q : ℕ) [Fact q.Prime]
    (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra A T] [CharP T q]
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (hΔq : IsUnit (W.map (frobenius T q)).Δ)
    (Φ : projModelCR W.toProjective ⟶ projModelCR (W.map (frobenius T q)).toProjective)
    (hΦ : Φ ≫ projModelStrCR (W.map (frobenius T q)).toProjective = projModelStrCR W.toProjective)
    (hZ : ∃ ψ : ZChartRing (W.map (frobenius T q)).toProjective →+* ZChartRing W.toProjective,
        ψ (xOverZ (W.map (frobenius T q)).toProjective) = xOverZ W.toProjective ^ q ∧
        ψ (yOverZ (W.map (frobenius T q)).toProjective) = yOverZ W.toProjective ^ q ∧
        zChartι W.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ zChartι (W.map (frobenius T q)).toProjective)
    (hY : ∃ ψ : OriginChartRing (W.map (frobenius T q)).toProjective →+* OriginChartRing W.toProjective,
        ψ (xOverY (W.map (frobenius T q)).toProjective) = xOverY W.toProjective ^ q ∧
        ψ (zOverY (W.map (frobenius T q)).toProjective) = zOverY W.toProjective ^ q ∧
        originChartι W.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ originChartι (W.map (frobenius T q)).toProjective)
    [IsFinite Φ]
    (B : Type) [CommRing B] [IsArtinianRing B] [IsLocalRing B] (ρ : T →+* B)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (projModelStrCR W.toProjective))
    (hx : (⟨x.1 ≫ Φ, by rw [Category.assoc, hΦ]; exact x.2⟩ :
        SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (projModelStrCR (W.map (frobenius T q)).toProjective)) =
      (𝒢 T (W.map (frobenius T q)) hΔq).one _) :
    (𝒢 T W hΔ).nsmul _ q x = (𝒢 T W hΔ).one _ := by sorry
