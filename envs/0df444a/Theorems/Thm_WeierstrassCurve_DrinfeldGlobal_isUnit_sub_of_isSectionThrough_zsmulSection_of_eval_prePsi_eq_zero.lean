-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isUnit_sub_of_isSectionThrough_zsmulSection_of_eval_prePsi_eq_zero
-- name    : WeierstrassCurve.DrinfeldGlobal.isUnit_sub_of_isSectionThrough_zsmulSection_of_eval_prePsi_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/a05cc1a7-1c63-5a47-a8fd-a7ce036802d3
-- title:
--   Unit difference of abscissae of distinct multiples of an ℓ-division point
-- statement:
--   Let $A$ be a commutative ring and let $\mathcal G$ be a family of group laws over $A$: an assignment, to every commutative $A$-algebra $T$, every projective Weierstrass curve $W$ over $T$ and every proof that the discriminant $W.\Delta$ is a unit, of a relative group law on the projective model of $W$ over $\operatorname{Spec} T$. Assume $\mathcal G$ is chord–tangent, i.e. for each such $T$, $W$, $h_\Delta$ there is an `ev` with `IsPointsEval W (𝒢 T W hΔ) ev`, and that its identity is the origin: for each such datum there is a ring homomorphism $\chi$ from the origin chart ring of $W$ to $T$ exhibiting the unit section `(𝒢 T W hΔ).one` as an origin-chart section and satisfying $\chi(xOverY)=\chi(zOverY)=0$. Let $\ell$ be a prime with $\ell\ge 3$, let $T$ be a commutative $A$-algebra in which $\ell$ is invertible, and let $W$ be a projective Weierstrass curve over $T$ with $W.\Delta$ a unit. Let $S$ be a section of the projective model over $\operatorname{Spec} T$ and $x,y\in T$ be such that $S$ passes through $(x,y)$ in the $Z$-chart: some ring homomorphism $\chi$ from the $Z$-chart ring (the degree-zero homogeneous localisation at the third coordinate) to $T$ factors $S$ through the chart immersion `zChartι` and satisfies $\chi(xOverZ)=x$, $\chi(yOverZ)=y$. Assume $x$ is a root of the division polynomial $W.\mathrm{pre}\Psi_\ell$. Let $a\in\mathbb Z$ with $\ell\nmid a$, $\ell\nmid a-1$, $\ell\nmid a+1$, and let $x',y'\in T$ be such that the $a$-th multiple `zsmulSection (𝒢 T W hΔ) a S` of $S$ (the $a$-fold iterate of the group law for $a\ge 0$, and its inverse for $a<0$) passes through $(x',y')$ in the same sense. Then $x-x'$ is a unit of $T$.
--
--   This is the relative (ring-theoretic) form of the statement that two distinct multiples $[a]S$, $S$ of a section of exact order $\ell$ have invertible difference of abscissae, the invertibility being checked at all residue fields, where $[a]\bar S=\pm\bar S$ would force $\ell\mid a\mp 1$. It is used in the construction of level structures on the auxiliary level-one modular curve, where denominators $x-x'$ must be inverted.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_isUnit_sub_of_isSectionThrough_zsmulSection_of_eval_prePsi_eq_zero.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

theorem WeierstrassCurve.DrinfeldGlobal.isUnit_sub_of_isSectionThrough_zsmulSection_of_eval_prePsi_eq_zero
    {A : Type} [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (T : Type) [CommRing T] [Algebra A T] (hℓT : IsUnit ((ℓ : ℕ) : T))
    (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ)
    (S : Section W) (x y : T) (hS : IsSectionThrough S x y) (hx : (W.preΨ ℓ).eval x = 0)
    (a : ℤ) (ha : ¬ ((ℓ : ℤ) ∣ a)) (ha₁ : ¬ ((ℓ : ℤ) ∣ a - 1)) (ha₂ : ¬ ((ℓ : ℤ) ∣ a + 1))
    (x' y' : T) (hS' : IsSectionThrough (ModularCurve.LevelRelabelling.zsmulSection (𝒢 T W hΔ) a S) x' y') :
    IsUnit (x - x') := by sorry
