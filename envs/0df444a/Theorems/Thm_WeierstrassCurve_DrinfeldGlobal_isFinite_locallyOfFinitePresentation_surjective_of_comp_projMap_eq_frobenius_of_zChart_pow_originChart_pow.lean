-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isFinite_locallyOfFinitePresentation_surjective_of_comp_projMap_eq_frobenius_of_zChart_pow_originChart_pow
-- name    : WeierstrassCurve.DrinfeldGlobal.isFinite_locallyOfFinitePresentation_surjective_of_comp_projMap_eq_frobenius_of_zChart_pow_originChart_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/c88fbb92-dbd2-50e1-b29b-5dedef813b3c
-- title:
--   Chartwise q-th-power morphism of Weierstrass models is finite and surjective
-- statement:
--   Let $q$ be a prime, $T$ a commutative ring of characteristic $q$ and $W$ a Weierstrass curve over $T$; write $W^{(q)}$ for the base change $W$ along the Frobenius endomorphism $t\mapsto t^{q}$ of $T$, and let $P(V)=\operatorname{Proj}$ of $\mathrm{MvPolynomial}(\mathrm{Fin}\,3,T)/(V.\mathrm{polynomial})$ with its quotient grading denote the projective model of a projective Weierstrass curve $V$. Suppose given: a morphism $\Phi : P(W)\to P(W^{(q)})$ that is a morphism over $\operatorname{Spec} T$, i.e. $\Phi$ followed by `projModelStrCR` of $W^{(q)}$ equals `projModelStrCR` of $W$; a graded ring homomorphism $\varphi$ from the grading of $P(W)$ to that of $P(W^{(q)})$ whose target irrelevant ideal is contained in the image under $\varphi$ of the source irrelevant ideal, and which is a coefficient homomorphism, that is, it sends the class of a constant $C(a)$ to the class of $C(a^{q})$ and fixes the classes of the three variables; an endomorphism $F$ of $P(W)$ such that for every characteristic-$q$ ring $B$ and every point $x:\operatorname{Spec} B\to P(W)$ one has $\operatorname{Spec}(\mathrm{Frob}_B)$ followed by $x$ equal to $x$ followed by $F$; and the factorisation $\Phi$ followed by $\operatorname{Proj}(\varphi)$ equals $F$. Suppose further that on the chart $D_+(Z)$ there is a ring homomorphism $\psi$ from the $Z$-chart ring of $W^{(q)}$ to that of $W$ with $\psi(X/Z)=(X/Z)^{q}$, $\psi(Y/Z)=(Y/Z)^{q}$, through which the $Z$-chart inclusion followed by $\Phi$ factors as $\operatorname{Spec}\psi$ followed by the $Z$-chart inclusion for $W^{(q)}$, and likewise on the chart $D_+(Y)$ with $X/Y\mapsto (X/Y)^{q}$ and $Z/Y\mapsto (Z/Y)^{q}$. Then $\Phi$ is finite, locally of finite presentation and surjective.
--
--   This records the geometric properties of the relative Frobenius morphism of a projective Weierstrass model in characteristic $q$, presented axiomatically: any morphism which restricts to $q$-th power maps in the two standard affine charts and factors the absolute Frobenius through the coefficient base change is finite, locally of finite presentation and surjective. It is used by [`WeierstrassCurve.DrinfeldGlobal.exists_map_frobenius_isFinite_surjective_zChart_pow_originChart_pow`](thm.html#WeierstrassCurve.DrinfeldGlobal.exists_map_frobenius_isFinite_surjective_zChart_pow_originChart_pow), which produces such a $\Phi$ from the absolute Frobenius together with the structure morphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_isFinite_locallyOfFinitePresentation_surjective_of_comp_projMap_eq_frobenius_of_zChart_pow_originChart_pow.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.isFinite_locallyOfFinitePresentation_surjective_of_comp_projMap_eq_frobenius_of_zChart_pow_originChart_pow
    (q : ℕ) [Fact q.Prime] (T : Type) [CommRing T] [CharP T q] (W : WeierstrassCurve T)
    (Φ : projModelCR W.toProjective ⟶ projModelCR (W.map (frobenius T q)).toProjective)
    (hΦ : Φ ≫ projModelStrCR (W.map (frobenius T q)).toProjective = projModelStrCR W.toProjective)
    (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (W.map (frobenius T q)).toProjective)
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map (frobenius T q)).toProjective) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ)
    (hcoef : IsCoefficientHom W.toProjective (frobenius T q) φ)
    (F : projModelCR W.toProjective ⟶ projModelCR W.toProjective)
    (hF : ∀ (B : Type) [CommRing B] [CharP B q] (x : Spec (CommRingCat.of B) ⟶ projModelCR W.toProjective),
      Spec.map (CommRingCat.ofHom (frobenius B q)) ≫ x = x ≫ F)
    (hΦF : Φ ≫ Proj.map φ hφ = F)
    (hZ : ∃ ψ : ZChartRing (W.map (frobenius T q)).toProjective →+* ZChartRing W.toProjective,
        ψ (xOverZ (W.map (frobenius T q)).toProjective) = xOverZ W.toProjective ^ q ∧
        ψ (yOverZ (W.map (frobenius T q)).toProjective) = yOverZ W.toProjective ^ q ∧
        zChartι W.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ zChartι (W.map (frobenius T q)).toProjective)
    (hY : ∃ ψ : OriginChartRing (W.map (frobenius T q)).toProjective →+* OriginChartRing W.toProjective,
        ψ (xOverY (W.map (frobenius T q)).toProjective) = xOverY W.toProjective ^ q ∧
        ψ (zOverY (W.map (frobenius T q)).toProjective) = zOverY W.toProjective ^ q ∧
        originChartι W.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ originChartι (W.map (frobenius T q)).toProjective) :
    IsFinite Φ ∧ LocallyOfFinitePresentation Φ ∧ Surjective Φ := by sorry
