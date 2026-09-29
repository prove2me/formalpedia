-- Prove2me | Theorems.Thm_WeierstrassProjModel_hom_ext_of_zChartIota_comp_eq
-- name    : WeierstrassProjModel.hom_ext_of_zChartIota_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/405d804c-15a4-5665-b582-451e57d34a0b
-- title:
--   Morphisms from a projective Weierstrass model are determined on the Z-chart
-- statement:
--   Let $T$ be a commutative ring and let $W$ be a Weierstrass curve over $T$, with no condition imposed on its coefficients or discriminant; let $W$.`toProjective` be the associated projective Weierstrass datum. The scheme `projModelCR W.toProjective` is $\operatorname{Proj}$ of the graded ring obtained from $T[X_0,X_1,X_2]$ by dividing out the homogeneous ideal `projModelHomogeneousIdealCR` of the model, graded by the images of the homogeneous pieces of $T[X_0,X_1,X_2]$ under the quotient map. Let $Y$ be a separated scheme and let $f,g : \mathtt{projModelCR } W.\mathtt{toProjective} \to Y$ be two morphisms of schemes. Assume that the composites of the chart morphism `zChartι W.toProjective` with $f$ and with $g$ agree, i.e. that $f$ and $g$ restrict to the same morphism along the $Z$-chart of the model. Then $f = g$.
--
--   This is the statement that the $Z$-chart of a projective Weierstrass model is schematically dense in the model, so that morphisms to a separated target are determined by their restriction to that affine chart; it is the scheme-theoretic substitute for a density argument, valid over an arbitrary base ring, where the model need not be reduced. It is used in the comparison of two projective Weierstrass models over an Artinian ring, to show that an isomorphism compatible with the zero sections is induced by a variable change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_hom_ext_of_zChartIota_comp_eq.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_PointChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassProjModel.hom_ext_of_zChartIota_comp_eq
    (T : Type) [CommRing T] (W : WeierstrassCurve T)
    {Y : Scheme} [Y.IsSeparated]
    (f g : projModelCR W.toProjective ⟶ Y)
    (h : zChartι W.toProjective ≫ f = zChartι W.toProjective ≫ g) : f = g := by sorry
