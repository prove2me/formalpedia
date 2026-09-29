-- Prove2me | Theorems.Thm_WeierstrassProjModel_kw_lrChart_negY_gen_ne_zero
-- name    : WeierstrassProjModel.kw_lrChart_negY_gen_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/a1dc7a4f-967d-56f9-95c7-24af52a1162a
-- title:
--   Nonvanishing of 2y+a₁x+a₃ in the Z-chart ring
-- statement:
--   Let $R$ be a commutative ring which is a domain and let $W$ be a Weierstrass curve over $R$ which is elliptic. Write $\mathcal{A}_i$ for the homogeneous localisation away from the class of $X_i$ of the graded ring $\mathrm{MvPolynomial}(\mathrm{Fin}\ 3, R)/(F)$, graded by the images of the homogeneous submodules of $\mathrm{MvPolynomial}(\mathrm{Fin}\ 3, R)$ under the quotient map, where $F$ is the homogeneous cubic attached to the projective Weierstrass equation of $W$ and the ideal is $\mathrm{span}\{F\}$; the $R$-algebra structure on $\mathcal{A}_i$ is the one coming from the degree-zero part. For indices $i,m$, the element $\mathrm{kw\_lrChart\_gen}\,W\,i\,m \in \mathcal{A}_i$ is the class of the fraction with numerator the degree-one element $X_m$ and denominator the degree-one element $X_i$. The assertion is that in $\mathcal{A}_2$, i.e. the chart away from $X_2 = Z$, the element
--   $$2\cdot (X_1/X_2) + a_1\cdot (X_0/X_2) + a_3$$
--   is nonzero, where $a_1, a_3$ are the corresponding coefficients of $W$ mapped into $\mathcal{A}_2$.
--
--   In affine coordinates $x = X/Z$, $y = Y/Z$ on the $Z$-chart of the projective model this is the statement that the formal partial derivative $\partial_Y$ of the Weierstrass cubic, namely $2y + a_1 x + a_3 = y - \mathrm{negY}(x,y)$, does not vanish identically on the curve over a domain. It is used to show that the generic point of the $Z$-chart is not equal to its own negative, hence that doubling the generic point does not land on the zero class.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_kw_lrChart_negY_gen_ne_zero.lean

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

theorem WeierstrassProjModel.kw_lrChart_negY_gen_ne_zero
    [IsDomain R] [W.IsElliptic] :
    (2 : (𝒜 (2 : Fin 3))) * kw_lrChart_gen W 2 1
      + (algebraMap R (𝒜 (2 : Fin 3)) W.a₁) * kw_lrChart_gen W 2 0
      + algebraMap R (𝒜 (2 : Fin 3)) W.a₃ ≠ 0 := by sorry
