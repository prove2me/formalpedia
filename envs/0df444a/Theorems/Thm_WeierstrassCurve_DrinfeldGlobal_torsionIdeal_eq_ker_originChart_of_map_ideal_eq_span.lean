-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_torsionIdeal_eq_ker_originChart_of_map_ideal_eq_span
-- name    : WeierstrassCurve.DrinfeldGlobal.torsionIdeal_eq_ker_originChart_of_map_ideal_eq_span
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/2ec99dfa-0499-571b-91f9-6533a69e2de9
-- title:
--   q-torsion equals the origin-chart kernel Spec T[[Z]]/(g)
-- statement:
--   Let $T$ be a Noetherian commutative ring and $W$ a Weierstrass curve over $T$ with invertible discriminant, with projective plane model $\mathrm{Proj}$ of the graded quotient ring and structural morphism `projModelStrCR W` to $\operatorname{Spec} T$. Let $G$ be a relative group law on this morphism (functorial multiplication, unit, inverse on sections over $\operatorname{Spec} T$-schemes, with group axioms and compatibility with base change), and assume there is a points-evaluation datum `ev` for $G$: a family of bijections, for every field $F$ over $T$, between $F$-valued sections and the chord–tangent group of $W$ base-changed to $F$, additive for $G$ and Galois-equivariant. Let $q>0$, let $g\in T[[Z]]$, and suppose $T[[Z]]/(g)$ is free over $T$ with basis indexed by $\mathrm{Fin}(q^2)$ given by the classes of $1,Z,\dots,Z^{q^2-1}$. Let $\Phi$ be a ring homomorphism from the origin chart ring `OriginChartRing W` (the degree-zero homogeneous localisation away from the coordinate $Y$) to $T[[Z]]$ sending the image of each $t\in T$ to the constant series $C\,t$ and sending $X/Y$ to $-Z$. Finally assume that the ideal of `torsionIdeal G q` — the kernel ideal sheaf data of the first projection from the fibre product of `G.schemeNsmul q` with the unit section, followed by `toPullbackId` — pulled back along the origin chart inclusion followed by `toPullbackId`, read on the whole of $\operatorname{Spec}(\mathrm{OriginChartRing}\,W)$ through `Scheme.ΓSpecIso` and pushed forward along $\Phi$, equals $(g)$. Then `torsionIdeal G q` is the kernel ideal sheaf data of the morphism $\operatorname{Spec}(T[[Z]]/(g))\to\operatorname{Spec}(\mathrm{OriginChartRing}\,W)$ induced by $\Phi$ followed by the quotient map, composed with the origin chart inclusion and `toPullbackId`.
--
--   This is the torsion half of the Katz–Mazur comparison between the $q$-torsion subscheme of an elliptic curve and the $q$-torsion of its formal group at the origin: once the torsion ideal is cut out near the origin by a single series $g$ whose quotient is free of rank $q^2$, the whole $q$-torsion lies in the origin chart and is the closed subscheme $\operatorname{Spec} T[[Z]]/(g)$. It is used in the construction of global Drinfeld bases, in `isDrinfeldBasis_of_reducesToOrigin_of_isDrinfeldBasisAdic_typeZero`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_torsionIdeal_eq_ker_originChart_of_map_ideal_eq_span.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.torsionIdeal_eq_ker_originChart_of_map_ideal_eq_span
    {T : Type u} [CommRing T] [IsNoetherianRing T] (W : WeierstrassCurve T) [W.IsElliptic]
    (G : RelativeGroupLaw T (projModelStrCR W)) (hGpts : ∃ ev, IsPointsEval W G ev)
    {q : ℕ} (hq : 0 < q) (g : PowerSeries T)
    (b : Module.Basis (Fin (q * q)) T (PowerSeries T ⧸ Ideal.span {g}))
    (hb : ∀ i, b i = Ideal.Quotient.mk (Ideal.span {g}) (PowerSeries.X ^ (i : ℕ)))
    (Φ : OriginChartRing W →+* PowerSeries T)
    (hΦsc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
      PowerSeries.C t)
    (hΦx : Φ (xOverY W) = - PowerSeries.X)
    (hJ : Ideal.map (Φ.comp (Scheme.ΓSpecIso (CommRingCat.of (OriginChartRing W))).hom.hom)
      (((torsionIdeal G q).comap (originChartι W ≫ toPullbackId)).ideal ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩) =
      Ideal.span {g}) :
    torsionIdeal G q =
      (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk (Ideal.span {g})).comp Φ)) ≫
        originChartι W ≫ toPullbackId).ker := by sorry
