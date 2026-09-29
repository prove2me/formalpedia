-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_of_specMap_fstHom_comp_eq_of_nsmul_eq_one
-- name    : WeierstrassCurve.DrinfeldGlobal.nsmul_eq_one_of_specMap_fstHom_comp_eq_of_nsmul_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/42d29136-4f72-57b4-a22b-19395bb4c8fc
-- title:
--   Multiplication by q kills first-order lifts of q-torsion
-- statement:
--   Let $A$ be a commutative ring and let $\mathcal{G}$ be a family of group laws on projective Weierstrass models over $A$-algebras: for every $A$-algebra $T$, every projective Weierstrass curve $W$ over $T$ and every proof that $W.\Delta$ is a unit, $\mathcal{G}$ provides a `RelativeGroupLaw` on the structure morphism `projModelStrCR W` from $\operatorname{Proj}$ of the graded quotient ring to $\operatorname{Spec} T$, that is, a multiplication, identity and inversion on sections over arbitrary bases satisfying associativity, unit and inverse laws together with compatibility under base change. Two hypotheses are imposed on the family: `IsChordTangent`, asserting that in each such case there is an `ev` with `IsPointsEval W (𝒢 T W hΔ) ev`, and `IsOriginIdentity`, asserting that in each such case the identity section admits a chart description, namely a ring homomorphism $\chi$ from `OriginChartRing W` to $T$ which is an `IsOriginChartSection` for the identity section of $\mathcal{G}\,T\,W\,h\Delta$ and sends both `xOverY W` and `zOverY W` to $0$. Fix a natural number $q$, an $A$-algebra $B$, a Weierstrass curve $V$ over $B$ whose discriminant $V.\Delta$ is a unit, a field $k$ of characteristic $q$ and a ring homomorphism $f : B \to k$. Write $G = \mathcal{G}\,B\,V\,h\Delta$. Let $Q_0$ be a section of the projective model of $V$ over the base morphism $\operatorname{Spec}(f)$, i.e. a morphism $\operatorname{Spec} k \to \operatorname{Proj}$ whose composite with `projModelStrCR V` is $\operatorname{Spec}(f)$, and assume the $q$-fold iterate `G.nsmul _ q Q₀` of the group law, computed from the identity by repeated multiplication by $Q_0$, equals the identity section. Let $Q$ be a section over the base morphism induced by $B \to k \to k[\varepsilon]$, where $k[\varepsilon]$ is the ring of dual numbers over $k$, and assume that $\operatorname{Spec}$ of the projection $k[\varepsilon] \to k$ followed by $Q$ equals $Q_0$. Then `G.nsmul _ q Q` is the identity section over $\operatorname{Spec} k[\varepsilon]$.
--
--   This is the infinitesimal rigidity of $q$-torsion in characteristic $q$: multiplication by $q$ has vanishing differential on the fibre, so a first-order deformation of a $q$-torsion point over $k$ remains killed by $q$ over the dual numbers. It is used in the construction of dual-number level structures, being cited by the two statements [`ModularCurve.LevelModuliPackageAbs.exists_algHom_dualNumber_of_represents_nsmul_eq_one_of_nthSeries_eq_mul_X_pow_gamma0Pow`](thm.html#ModularCurve.LevelModuliPackageAbs.exists_algHom_dualNumber_of_represents_nsmul_eq_one_of_nthSeries_eq_mul_X_pow_gamma0Pow) and [`ModularCurve.LevelModuliPackageAbs.exists_algHom_dualNumber_of_represents_nsmul_eq_one_of_nthSeries_eq_mul_X_pow_rigidDataH1Pow`](thm.html#ModularCurve.LevelModuliPackageAbs.exists_algHom_dualNumber_of_represents_nsmul_eq_one_of_nthSeries_eq_mul_X_pow_rigidDataH1Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_of_specMap_fstHom_comp_eq_of_nsmul_eq_one.lean

import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing FormalGroup
attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.nsmul_eq_one_of_specMap_fstHom_comp_eq_of_nsmul_eq_one
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity) (q : ℕ)
    (B : Type) [CommRing B] [Algebra A B] (V : WeierstrassCurve B) (hΔ : IsUnit V.Δ)
    (k : Type) [Field k] [CharP k q] (f : B →+* k)
    (Q₀ : SchemeHomOver (Spec.map (CommRingCat.ofHom f)) (projModelStrCR V))
    (hQ₀ : (𝒢 B V hΔ).nsmul _ q Q₀ = (𝒢 B V hΔ).one _)
    (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap k (DualNumber k)).comp f))) (projModelStrCR V))
    (hQ : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ Q.1 = Q₀.1) :
    (𝒢 B V hΔ).nsmul _ q Q = (𝒢 B V hΔ).one _ := by sorry
