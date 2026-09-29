-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comp_schemeNsmul_eq_one_of_comp_eq_one_of_zChart_pow_originChart_pow
-- name    : WeierstrassCurve.DrinfeldGlobal.comp_schemeNsmul_eq_one_of_comp_eq_one_of_zChart_pow_originChart_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/49300d0f-cb40-5af4-9d17-7b3c4ccd70e3
-- title:
--   Multiplication by q kills the kernel of Φ
-- statement:
--   Let $A$ be a commutative ring and let $\mathcal G$ be a family of relative group laws assigning, to every $A$-algebra $T$ and every projective Weierstrass curve $W$ over $T$ with $\Delta(W)$ a unit, a relative group law on the structure morphism `projModelStrCR` of the Proj model of $W$; assume $\mathcal G$ is chord-tangent (for all such $T,W,\Delta$ a points-evaluation `ev` exists, in the sense of `IsPointsEval`) and origin-identity (its identity section arises from a ring homomorphism $\chi$ on the origin chart $\mathrm{Away}$-ring killing $x/y$ and $z/y$). Let $q$ be a prime, $T$ an Artinian local $A$-algebra of characteristic $q$, and $W$ a Weierstrass curve over $T$ such that both $\Delta(W)$ and the discriminant of the Frobenius twist $W^{(q)} = W.\mathrm{map}(\mathrm{frobenius}\,T\,q)$ are units. Let $\Phi$ be a finite morphism from the Proj model of $W$ to that of $W^{(q)}$ commuting with the two structure morphisms to $\mathrm{Spec}\,T$, and assume that on the $Z$-chart and on the origin chart $\Phi$ is induced by ring homomorphisms sending $x/z, y/z$ and $x/y, z/y$ respectively to their $q$-th powers, compatibly with the chart immersions `zChartι`, `originChartι`. Then for every scheme $S$, every $t : S \to \mathrm{Spec}\,T$ and every section $x$ of the Proj model of $W$ over $t$, if $x$ followed by $\Phi$ is the identity section of $\mathcal G(T,W^{(q)})$ over $t$, then $x$ followed by the $q$-fold multiplication endomorphism `schemeNsmul q` of $\mathcal G(T,W)$ is the identity section of $\mathcal G(T,W)$ over $t$.
--
--   This is the statement that multiplication by $q$ annihilates the kernel of the relative Frobenius $\Phi$, here over an arbitrary test scheme rather than only over Artinian local points. It feeds the construction of a variable change realising the Frobenius-kernel quotient, used in the analysis of level-$q$ structures on Weierstrass models in characteristic $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_comp_schemeNsmul_eq_one_of_comp_eq_one_of_zChart_pow_originChart_pow.lean

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

theorem WeierstrassCurve.DrinfeldGlobal.comp_schemeNsmul_eq_one_of_comp_eq_one_of_zChart_pow_originChart_pow
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
    {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T)) (x : SchemeHomOver t (projModelStrCR W.toProjective))
    (hx : (⟨x.1 ≫ Φ, by rw [Category.assoc, hΦ]; exact x.2⟩ : SchemeHomOver t (projModelStrCR (W.map (frobenius T q)).toProjective)) =
      (𝒢 T (W.map (frobenius T q)) hΔq).one t) :
    (⟨x.1 ≫ (𝒢 T W hΔ).schemeNsmul q, by rw [Category.assoc, (𝒢 T W hΔ).schemeNsmul_over]; exact x.2⟩ :
        SchemeHomOver t (projModelStrCR W.toProjective)) = (𝒢 T W hΔ).one t := by sorry
