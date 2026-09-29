-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_nsmul_two_eq_one_iff_of_isSectionThrough
-- name    : WeierstrassCurve.DrinfeldGlobal.nsmul_two_eq_one_iff_of_isSectionThrough
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/99bb32c1-b9a5-5722-888c-949d98bab0fd
-- title:
--   Two-torsion criterion for a section through an affine point
-- statement:
--   Let $A$ be a commutative ring and let $\mathcal{G}$ be a family of relative group laws over $A$: for every commutative $A$-algebra $T$, every projective Weierstrass curve $W$ over $T$ and every proof that the discriminant $W.\Delta$ is a unit, $\mathcal{G}$ provides a relative group law on the projective model $\mathrm{Proj}$ of $W$ over $\mathrm{Spec}\,T$ (multiplication, unit and inverse on sections over arbitrary bases, associative, unital, with inverses, and compatible with base change). Assume $\mathcal{G}$ is chord–tangent, i.e. for each such $T$, $W$ and unit discriminant there is an identification $\mathrm{ev}$ of sections over field points with the affine points of the base-changed curve satisfying `IsPointsEval`, and that $\mathcal{G}$ has origin identity, i.e. for each such datum there is a ring homomorphism $\chi$ from the origin chart ring of $W$ to $T$ cutting out the unit section with $\chi(x/y)=\chi(z/y)=0$. Let $T$ be a commutative $A$-algebra in which $2$ is a unit, let $W$ be a projective Weierstrass curve over $T$ with $W.\Delta$ a unit, let $S$ be a $T$-section of the projective model, and let $x,y\in T$ be such that $S$ passes through $(x,y)$, that is, $S$ factors through the chart where the last coordinate is inverted via a ring homomorphism $\chi$ with $\chi(x/z)=x$ and $\chi(y/z)=y$. Then $S$ added to itself twice in the group law $\mathcal{G}\,T\,W$ (over the identity base map) equals the unit section if and only if $2y + a_1 x + a_3 = 0$ in $T$.
--
--   This is the level-$2$ case of the torsion dictionary for the relative group law on a Weierstrass projective model: an affine section is killed by $2$ exactly when it is fixed by negation, the vanishing of the honest $2$-division expression $\psi_2 = 2y + a_1x + a_3$. It feeds the construction and counting of Drinfeld level-$2$ structures, being used in the unique-lifting statement for level structures and in the computation of the number of raw Drinfeld pairs of level $2$ over an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_nsmul_two_eq_one_iff_of_isSectionThrough.lean

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.nsmul_two_eq_one_iff_of_isSectionThrough
    {A : Type} [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (T : Type) [CommRing T] [Algebra A T] (h2T : IsUnit ((2 : ℕ) : T))
    (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ)
    (S : Section W) (x y : T) (hS : IsSectionThrough S x y) :
    (𝒢 T W hΔ).nsmul (𝟙 _) 2 S = (𝒢 T W hΔ).one (𝟙 _) ↔ 2 * y + W.a₁ * x + W.a₃ = 0 := by sorry
