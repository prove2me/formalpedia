-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_iff_X_sub_C_originParam_dvd_nthSeries
-- name    : WeierstrassCurve.DrinfeldGlobal.nsmul_eq_one_iff_X_sub_C_originParam_dvd_nthSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/3705340b-0734-5985-b891-3f09ddbc7377
-- title:
--   Torsion at the origin and divisibility of [q]_F
-- statement:
--   Let $T$ be a commutative Noetherian local ring that is adically complete for its maximal ideal, and let $W$ be a Weierstrass curve over $T$ which is elliptic. Let $F$ be a formal group over $T$ whose underlying two-variable power series is $W$'s fixed-coordinate formal group law `W.formalGroupLawFixed`, and let $G$ be a relative group law on the structure morphism `projModelStrCR W` of the graded projective model of $W$ over $\operatorname{Spec} T$ (a functorial multiplication, unit and inverse on $T$-scheme sections satisfying associativity, unit and inverse laws and compatibility with base change). Assume: there is a family of bijections, for fields $F$ over $T$, between sections over $\operatorname{Spec} F$ and the affine points of $W_F$ which turns $G$'s multiplication into addition of points and is equivariant for $T$-algebra automorphisms; and there is a ring homomorphism $\chi$ from the origin chart ring (the degree-zero localisation away from the second coordinate) to $T$ which presents the unit section $G.\mathrm{one}(\mathbb{1})$ as $\operatorname{Spec}\chi$ followed by the origin chart immersion and satisfies $\chi(x/y)=\chi(z/y)=0$. Let $q\in\mathbb{N}$, let $P$ be a section of the model over the identity of $\operatorname{Spec} T$, and let $\chi_P$ be a ring homomorphism from the origin chart ring to $T$ presenting $P$ in the origin chart, with $\mathrm{originParam}\,\chi_P=-\chi_P(x/y)$ and $\mathrm{originW}\,\chi_P$ both in the maximal ideal of $T$. Then the $q$-fold $G$-sum of $P$ (iterated $G$-multiplication starting from the unit section) equals the unit section if and only if $X-C(\mathrm{originParam}\,\chi_P)$ divides `F.nthSeries q` in $T[[X]]$, where `nthSeries` is defined by $0\mapsto 0$ and $n+1\mapsto$ the substitution of $(\mathrm{nthSeries}\,n, X)$ into the group law of $F$.
--
--   This is the dictionary between torsion in the global group law on the projective model and the multiplication-by-$q$ series of the associated formal group: a section reducing to the origin is killed by $q$ exactly when its formal parameter is a root of $[q]_F$, expressed as divisibility by the degree-one distinguished polynomial $X-C(z)$. It is used in the analysis of torsion sections lifting from the special fibre of an elliptic curve over a complete local base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_iff_X_sub_C_originParam_dvd_nthSeries.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.nsmul_eq_one_iff_X_sub_C_originParam_dvd_nthSeries
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (W : WeierstrassCurve T) [W.IsElliptic]
    (F : FormalGroup T) (hFW : F.toPowerSeries = W.formalGroupLawFixed)
    (G : RelativeGroupLaw T (projModelStrCR W))
    (hGpts : ∃ ev, IsPointsEval W G ev)
    (hGone : ∃ χ : OriginChartRing W →+* T,
      IsOriginChartSection (G.one (𝟙 _)) χ ∧ χ (xOverY W) = 0 ∧ χ (zOverY W) = 0)
    (q : ℕ) (P : Section W) (χP : OriginChartRing W →+* T) (hP : ReducesToOrigin P χP (maximalIdeal T)) :
    G.nsmul (𝟙 _) q P = G.one (𝟙 _) ↔
      (PowerSeries.X - PowerSeries.C (originParam χP)) ∣ F.nthSeries q := by sorry
