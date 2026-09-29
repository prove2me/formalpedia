-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isFinite_pullback_snd_kwZeroSect_flat_finrank_eq_of_zChart_pow_originChart_pow
-- name    : WeierstrassCurve.DrinfeldGlobal.isFinite_pullback_snd_kwZeroSect_flat_finrank_eq_of_zChart_pow_originChart_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/e20c5bb3-a6b5-5298-890a-b7305c5a21fe
-- title:
--   Frobenius kernel on a Weierstrass model is finite flat of rank q
-- statement:
--   Let $q$ be a prime, let $T$ be a commutative ring of characteristic $q$, and let $W$ be a Weierstrass curve over $T$, with Frobenius twist $W^{(q)} := W.\mathrm{map}(\mathrm{frobenius}\ T\ q)$. Let $\Phi$ be a morphism from the $\mathrm{Proj}$ of the graded quotient ring attached to the projective Weierstrass model of $W$ to the corresponding $\mathrm{Proj}$ for $W^{(q)}$, and assume: (hΦ) $\Phi$ followed by the structure morphism of the model of $W^{(q)}$ to $\mathrm{Spec}\,T$ equals the structure morphism for $W$; (hZ) there is a ring homomorphism $\psi$ from the $Z$-chart ring of $W^{(q)}$ (the homogeneous localisation away from the class of $X_2$) to that of $W$ with $\psi(X/Z) = (X/Z)^q$, $\psi(Y/Z) = (Y/Z)^q$, and such that the $Z$-chart immersion for $W$ followed by $\Phi$ equals $\mathrm{Spec}\,\psi$ followed by the $Z$-chart immersion for $W^{(q)}$; (hY) the analogous data on the origin chart (homogeneous localisation away from the class of $X_1$), with $\psi(X/Y) = (X/Y)^q$ and $\psi(Z/Y) = (Z/Y)^q$ and the same compatibility with the origin-chart immersions. Then the second projection of the fibre product of $\Phi$ with the underlying morphism of the zero section $\mathrm{kwZeroSect}$ of the model of $W^{(q)}$ is finite, flat and locally of finite presentation, and its $\mathrm{finrank}$ at every point $s$ equals $q$.
--
--   This is the assertion that the scheme-theoretic kernel of a relative Frobenius morphism on a projective Weierstrass model — the pullback of the zero section along $\Phi$ — is a finite flat group-scheme-sized object of constant rank $q$ over the base, with no smoothness or group-law hypothesis on $W$. It feeds the construction of the canonical isomorphism between a Weierstrass model and the double twist of its Frobenius quotient, used in [`WeierstrassCurve.DrinfeldGlobal.exists_iso_projModelCR_map_map_of_frobenius_of_comp_schemeNsmul_eq_one_of_nsmul_eq_one`](thm.html#WeierstrassCurve.DrinfeldGlobal.exists_iso_projModelCR_map_map_of_frobenius_of_comp_schemeNsmul_eq_one_of_nsmul_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_isFinite_pullback_snd_kwZeroSect_flat_finrank_eq_of_zChart_pow_originChart_pow.lean

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
open CategoryTheory.Limits in

theorem WeierstrassCurve.DrinfeldGlobal.isFinite_pullback_snd_kwZeroSect_flat_finrank_eq_of_zChart_pow_originChart_pow
    (q : ℕ) [Fact q.Prime] (T : Type) [CommRing T] [CharP T q] (W : WeierstrassCurve T)
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
    IsFinite (pullback.snd Φ (kwZeroSect T (W.map (frobenius T q))).1) ∧ Flat (pullback.snd Φ (kwZeroSect T (W.map (frobenius T q))).1) ∧
      LocallyOfFinitePresentation (pullback.snd Φ (kwZeroSect T (W.map (frobenius T q))).1) ∧
      ∀ s, (pullback.snd Φ (kwZeroSect T (W.map (frobenius T q))).1).finrank s = q := by sorry
