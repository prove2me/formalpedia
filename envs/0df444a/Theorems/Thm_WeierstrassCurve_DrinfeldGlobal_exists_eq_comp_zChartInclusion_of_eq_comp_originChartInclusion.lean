-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_eq_comp_zChartInclusion_of_eq_comp_originChartInclusion
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_eq_comp_zChartInclusion_of_eq_comp_originChartInclusion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/ce07cc0d-502f-5b2f-b94b-bef0e0b06348
-- title:
--   Rechartering a field point from D₊(Y) to D₊(Z)
-- statement:
--   Let $T$ be a commutative ring, $W$ a Weierstrass curve over $T$, and $F$ a field (in the same universe). Write $\mathrm{Proj}$ for `projModelCR W.toProjective`, the Proj of the quotient grading of the homogeneous coordinate ring of the projective Weierstrass model of $W$, with homogeneous coordinates `coord W.toProjective i` for $i \in \{0,1,2\}$, that is $X$, $Y$, $Z$. Let $p : \operatorname{Spec} F \to \mathrm{Proj}$ be a morphism of schemes and let $\chi :$ `OriginChartRing W` $\to F$ be a ring homomorphism from the degree-zero homogeneous localisation at $Y$ (the coordinate ring of the standard open $D_+(Y)$). Assume that $p$ equals $\operatorname{Spec}$ of $\chi$ followed by the inclusion `originChartι W` of that chart into $\mathrm{Proj}$, and that $\chi(Z/Y) \ne 0$, where `zOverY W` is the class of $Z/Y$. Then there is a ring homomorphism $\chi'$ from `ZChartRing W.toProjective`, the degree-zero homogeneous localisation at $Z$, to $F$ such that $p$ equals $\operatorname{Spec}$ of $\chi'$ followed by the chart inclusion `zChartι W.toProjective`, and moreover $\chi'(X/Z) = \chi(X/Y)/\chi(Z/Y)$ and $\chi'(Y/Z) = 1/\chi(Z/Y)$, where `xOverZ` and `yOverZ` denote the classes of $X/Z$ and $Y/Z$.
--
--   This is the passage of a field-valued point of the projective Weierstrass model from the chart around the point at infinity to the finite chart, in the standard-open form familiar from the description of $\mathrm{Proj}$ by the opens $D_+(f)$: a point of $D_+(Y)$ at which $Z/Y$ is invertible lies in $D_+(Z)$, with the expected coordinates. It is used in the construction of the formal group law of the curve, where data given in terms of the parameter at the origin must be read off in the coordinates of the finite chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_eq_comp_zChartInclusion_of_eq_comp_originChartInclusion.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_eq_comp_zChartInclusion_of_eq_comp_originChartInclusion
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) {F : Type u} [Field F]
    (p : Spec (CommRingCat.of F) ⟶ projModelCR W.toProjective) (χ : OriginChartRing W →+* F)
    (hp : p = Spec.map (CommRingCat.ofHom χ) ≫ originChartι W) (hv : χ (zOverY W) ≠ 0) :
    ∃ χ' : ZChartRing W.toProjective →+* F,
      p = Spec.map (CommRingCat.ofHom χ') ≫ zChartι W.toProjective ∧
      χ' (xOverZ W.toProjective) = χ (xOverY W) / χ (zOverY W) ∧
      χ' (yOverZ W.toProjective) = 1 / χ (zOverY W) := by sorry
