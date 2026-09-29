-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_section_reducesToOrigin_originParam_eq
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_section_reducesToOrigin_originParam_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/8fcb1d1e-e824-593e-b236-c5e1cb379484
-- title:
--   Sections with prescribed origin parameter over complete local rings
-- statement:
--   Let $T$ be a commutative local ring that is adically complete for its maximal ideal $\mathfrak{m}_T$, let $W$ be a Weierstrass curve over $T$, and let $z \in \mathfrak{m}_T$. The assertion is that there exist a section $P$ and a ring homomorphism $\chi : \mathrm{OriginChartRing}\,W \to T$ with the following properties. Here a `Section` of $W$ is a morphism $\varphi$ from $\mathrm{Spec}\,T$ to $\mathrm{Proj}$ of the graded ring $\mathrm{projModelGradingCR}\,W$ — the grading induced on the quotient of $R[X_0,X_1,X_2]$ by the homogeneous Weierstrass ideal of $W$ — together with the condition that $\varphi$ followed by the structure morphism `projModelStrCR W` is the identity of $\mathrm{Spec}\,T$; and $\mathrm{OriginChartRing}\,W$ is the degree-zero homogeneous localisation of that graded quotient away from the coordinate $\mathrm{coord}\,W\,1$, i.e. away from $Y$. The two conditions are: `ReducesToOrigin P χ (maximalIdeal T)`, that is, the morphism underlying $P$ equals $\mathrm{Spec}(\chi)$ followed by the open immersion `originChartι W` of the chart, and both $\mathrm{originParam}\,\chi = -\chi(X_0/X_1)$ and $\mathrm{originW}\,\chi = -\chi(X_2/X_1)$ lie in $\mathfrak{m}_T$; and in addition $\mathrm{originParam}\,\chi = z$. Only existence is asserted, no uniqueness.
--
--   This is the standard statement that, over a complete local ring, every element of the maximal ideal occurs as the value $-x/y$ of a point of the Weierstrass model lying in the formal neighbourhood of the origin, the companion value $-1/y$ being obtained from the formal-group power series. It supplies points to the criterion [`WeierstrassCurve.DrinfeldGlobal.isDrinfeldBasis_iff_eval_originParam_eq_zero_and_exists_section_of_nthSeries_eq_X_mul_mul_of_forall_nthSeries_eq_mul_prod`](thm.html#WeierstrassCurve.DrinfeldGlobal.isDrinfeldBasis_iff_eval_originParam_eq_zero_and_exists_section_of_nthSeries_eq_X_mul_mul_of_forall_nthSeries_eq_mul_prod) and to the adic Drinfeld-basis comparisons at level $\Gamma_0(p^n)$ and for the rigid data used there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_section_reducesToOrigin_originParam_eq.lean

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

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_section_reducesToOrigin_originParam_eq
    {T : Type u} [CommRing T] [IsLocalRing T] [IsAdicComplete (maximalIdeal T) T]
    (W : WeierstrassCurve T) (z : T) (hz : z ∈ maximalIdeal T) :
    ∃ (P : Section W) (χ : OriginChartRing W →+* T),
      ReducesToOrigin P χ (maximalIdeal T) ∧ originParam χ = z := by sorry
