-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_originChart_comp_schemeNsmul_eq_of_formalChart
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_originChart_comp_schemeNsmul_eq_of_formalChart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/04ddd5ea-2a39-594a-a0b4-470bdb537f5d
-- title:
--   Multiplication by q on the formal point at the origin
-- statement:
--   Let $T$ be a commutative Noetherian local ring that is adically complete for its maximal ideal, and let $W$ be a Weierstrass curve over $T$ with invertible discriminant. Let $F$ be a formal group over $T$ whose underlying two-variable power series is $W$'s normalised formal group law `W.formalGroupLawFixed`, and let $G$ be a relative group law on the projective Weierstrass model structure morphism `projModelStrCR W`, that is, a functorial abelian group structure on the sets of sections of that morphism. Assume: $G$ admits a points evaluation, i.e. a family of bijections, for every field $F$ with $T$-algebra structure, between the $\mathrm{Spec} F$-sections and the points of the affine curve $W$ base changed to $F$, additive for $G$ and equivariant for $T$-automorphisms of $F$; and the unit section $G.\mathrm{one}(\mathbf 1)$ factors through the chart `originChartι W` where $y$ is inverted, via a ring homomorphism `OriginChartRing W` $\to T$ killing both $x/y$ and $z/y$. Fix $q\in\mathbb N$ and a ring homomorphism $\Phi :$ `OriginChartRing W` $\to T[[X]]$ which sends the degree-zero image of each $t\in T$ to the constant series $t$, with $\Phi(x/y)=-X$ and $\Phi(z/y)=-W.\mathrm{formalW}$. Then there is a ring homomorphism $\chi :$ `OriginChartRing W` $\to T[[X]]$, again sending constants to constants, such that $\mathrm{Spec}(\Phi)$ followed by the chart inclusion followed by the $q$-fold sum endomorphism `G.schemeNsmul q` equals $\mathrm{Spec}(\chi)$ followed by the chart inclusion, and $\chi(x/y)=-[q]_F$, $\chi(z/y)=-W.\mathrm{formalW}\bigl([q]_F\bigr)$, where $[q]_F$ is `F.nthSeries q`, defined by $[0]_F=0$ and $[n+1]_F=F([n]_F,X)$.
--
--   This identifies the effect of multiplication by $q$ on the scheme-theoretic model with the multiplication-by-$q$ series of the formal group, in the chart at the origin: the universal formal point $(-X,-w_W(X))$ is carried to $(-[q]_F(X),-w_W([q]_F(X)))$. It is the computational core of the description of the ideal of $q$-torsion near the origin, and is used by [`WeierstrassCurve.DrinfeldGlobal.map_ideal_comap_torsionIdeal_eq_span_nthSeries`](thm.html#WeierstrassCurve.DrinfeldGlobal.map_ideal_comap_torsionIdeal_eq_span_nthSeries).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_originChart_comp_schemeNsmul_eq_of_formalChart.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_originChart_comp_schemeNsmul_eq_of_formalChart
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (W : WeierstrassCurve T) [W.IsElliptic]
    (F : FormalGroup T) (hFW : F.toPowerSeries = W.formalGroupLawFixed)
    (G : RelativeGroupLaw T (projModelStrCR W))
    (hGpts : ∃ ev, IsPointsEval W G ev)
    (hGone : ∃ χ : OriginChartRing W →+* T,
      IsOriginChartSection (G.one (𝟙 _)) χ ∧ χ (xOverY W) = 0 ∧ χ (zOverY W) = 0)
    (q : ℕ)
    (Φ : OriginChartRing W →+* PowerSeries T)
    (hΦsc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
      PowerSeries.C t)
    (hΦx : Φ (xOverY W) = - PowerSeries.X) (hΦz : Φ (zOverY W) = - W.formalW) :
    ∃ χ : OriginChartRing W →+* PowerSeries T,
      (∀ t : T, χ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
        PowerSeries.C t) ∧
      Spec.map (CommRingCat.ofHom Φ) ≫ originChartι W ≫ G.schemeNsmul q =
        Spec.map (CommRingCat.ofHom χ) ≫ originChartι W ∧
      χ (xOverY W) = - F.nthSeries q ∧
      χ (zOverY W) = - PowerSeries.subst (F.nthSeries q) W.formalW := by sorry
