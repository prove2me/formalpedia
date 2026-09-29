-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_originChart_rel
-- name    : WeierstrassCurve.DrinfeldGlobal.originChart_rel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/b2dd9026-c7cd-53f0-8a54-53afec686cfd
-- title:
--   Dehomogenised Weierstrass relation in the origin chart
-- statement:
--   Let $T$ be a commutative ring and $W$ a Weierstrass curve over $T$, regarded through the coercion as a projective Weierstrass cubic, so that the graded ring attached to it is $T[X_0,X_1,X_2]/(F_W)$ with the grading $\mathtt{projModelGradingCR}\,W$ obtained by pushing the submodules of homogeneous polynomials of each degree forward along the quotient map, and let $\mathtt{OriginChartRing}\,W$ be the degree-zero homogeneous localisation of this graded ring away from the class $\mathtt{coord}\,W\,1$ of $X_1$, i.e. the coordinate ring of the chart $D_+(Y)$ of the projective model. Inside it, `xOverY W` and `zOverY W` are the elements $X/Y$ and $Z/Y$, each written as a degree-one numerator over the first power of $\mathtt{coord}\,W\,1$. Let $B$ be a commutative ring which is a $T$-algebra and let $\chi : \mathtt{OriginChartRing}\,W \to B$ be a ring homomorphism which is compatible with scalars, in the sense that for every $t \in T$ the image under $\chi$ of the element of the chart ring coming from $t$ via the degree-zero part of the grading equals $\mathrm{algebraMap}_{T,B}(t)$. Writing $u = \chi(X/Y)$ and $v = \chi(Z/Y)$ and denoting by $a_i$ the images in $B$ of the coefficients of $W$, the conclusion is the identity $$v + a_1 u v + a_3 v^2 = u^3 + a_2 u^2 v + a_4 u v^2 + a_6 v^3.$$
--
--   This is the Weierstrass equation $Y^2Z + a_1XYZ + a_3YZ^2 = X^3 + a_2X^2Z + a_4XZ^2 + a_6Z^3$ divided by $Y^3$, i.e. the defining relation between the standard parameters $X/Y$ and $Z/Y$ at the origin of the projective model, transported along an arbitrary scalar-compatible ring map out of the chart ring. It is used on the passage from the global model to the formal group at the origin, for instance in identifying the kernel of such a chart map with an explicit ideal and in the comparison of chart parameters with the formal group law.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_originChart_rel.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing
  HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.originChart_rel
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) {B : Type u} [CommRing B] [Algebra T B]
    (χ : OriginChartRing W →+* B)
    (hsc : ∀ t : T, χ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
      algebraMap T B t) :
    χ (zOverY W) + algebraMap T B W.a₁ * χ (xOverY W) * χ (zOverY W) + algebraMap T B W.a₃ * χ (zOverY W) ^ 2 =
      χ (xOverY W) ^ 3 + algebraMap T B W.a₂ * χ (xOverY W) ^ 2 * χ (zOverY W) +
        algebraMap T B W.a₄ * χ (xOverY W) * χ (zOverY W) ^ 2 + algebraMap T B W.a₆ * χ (zOverY W) ^ 3 := by sorry
