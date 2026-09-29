-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_section_reducesToOrigin_originParam_eq_X
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_section_reducesToOrigin_originParam_eq_X
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/078a6e22-6cd4-586f-a4f6-d0b261de7ef4
-- title:
--   Section with formal parameter Xᵢ over A[[X₀,X₁]]
-- statement:
--   Let $A$ be a commutative ring, $W$ a Weierstrass curve over $A$, and $i \in \{0,1\}$. Write $R = A[\![X_0,X_1]\!]$ for the ring `MvPowerSeries (Fin 2) A` and $W'$ for the base change of $W$ along $A \to R$, regarded as a projective Weierstrass curve. The assertion is that there exist a section $P$ of the projective Weierstrass model of $W'$, that is, a morphism $\operatorname{Spec} R \to \operatorname{Proj}$ of the graded quotient ring of $W'$ whose composite with the structure morphism `projModelStrCR` is the identity of $\operatorname{Spec} R$, together with a ring homomorphism $\chi$ from the origin chart ring of $W'$ (the degree-zero homogeneous localisation of the graded coordinate ring at the class of the variable $Y$) to $R$, such that: the underlying morphism of $P$ is $\operatorname{Spec}$ of $\chi$ followed by the chart inclusion `originChartι`; the two elements $-\chi(x/y)$ and $-\chi(z/y)$ both lie in the ideal $(X_0, X_1)$ of $R$; and moreover $-\chi(x/y) = X_i$ exactly. The last equality makes the first of the two membership conditions automatic.
--
--   This produces, over the two-variable power series ring, the point of the Weierstrass model lying in the chart about the origin whose formal parameter $z = -x/y$ is precisely the coordinate $X_i$, the tautological input for the Weierstrass parametrisation $(z, w(z))$ of the formal group. It is used in the construction of formal addition, via [`WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_mul_originParam_eq_eval`](thm.html#WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_mul_originParam_eq_eval).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_section_reducesToOrigin_originParam_eq_X.lean

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

theorem WeierstrassCurve.DrinfeldGlobal.exists_section_reducesToOrigin_originParam_eq_X
    {A : Type} [CommRing A] (W : WeierstrassCurve A) (i : Fin 2) :
    ∃ (P : Section (W.map (algebraMap A (MvPowerSeries (Fin 2) A))))
      (χ : OriginChartRing (W.map (algebraMap A (MvPowerSeries (Fin 2) A))) →+* MvPowerSeries (Fin 2) A),
      ReducesToOrigin P χ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) A), MvPowerSeries.X 1}) ∧
      originParam χ = MvPowerSeries.X i := by sorry
