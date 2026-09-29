-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_iff_eval_prePsi_eq_zero_of_isSectionThrough
-- name    : WeierstrassCurve.DrinfeldGlobal.nsmul_eq_one_iff_eval_prePsi_eq_zero_of_isSectionThrough
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/8cf587d9-4cab-5f75-9853-eb500ced07bd
-- title:
--   ℓ-torsion of a section versus vanishing of preΨ_ℓ
-- statement:
--   Let $A$ be a commutative ring and let $\mathcal G$ be a family of group laws over $A$: for every commutative $A$-algebra $T$, every projective Weierstrass curve $W$ over $T$ and every proof that $\Delta(W)$ is a unit, a relative group law $\mathcal G\,T\,W\,h_\Delta$ on the structure morphism `projModelStrCR W` of the projective model. Assume $\mathcal G$ is chord–tangent, i.e. for each such $T,W,h_\Delta$ there is a family of bijections $\mathrm{ev}$ from sections over field-valued points to the affine point group of the corresponding base change satisfying `IsPointsEval`; and assume $\mathcal G$ has the origin as identity, i.e. for each such $T,W,h_\Delta$ there is a ring homomorphism $\chi$ from the origin chart ring of $W$ to $T$ which realises the unit section $\mathcal G\,T\,W\,h_\Delta{.}\mathrm{one}(\mathbb 1)$ as an origin-chart section and kills both $x/y$ and $z/y$. Let $\ell$ be a prime with $\ell \neq 2$, let $T$ be a commutative $A$-algebra in which $\ell$ is a unit, let $W$ be a projective Weierstrass curve over $T$ with $\Delta(W)$ a unit, and let $S$ be a $T$-section of the projective model of $W$ passing through $(x,y) \in T^2$, meaning that there is a ring homomorphism $\chi$ from the degree-zero homogeneous localisation away from the third coordinate to $T$ with $S$ equal to $\mathrm{Spec}(\chi)$ followed by the inclusion of that chart, and $\chi(x/z) = x$, $\chi(y/z) = y$. Then the $\ell$-fold iterate of the group law $\mathcal G\,T\,W\,h_\Delta$ applied to $S$ equals its unit section if and only if $(W.\mathrm{pre}\Psi\;\ell)$ evaluated at $x$ is $0$.
--
--   This is the division-polynomial criterion for $\ell$-torsion in its relative form: over a base in which both $\ell$ and the discriminant are invertible, a section through an affine point $(x,y)$ is killed by $\ell$ for the given family of group laws exactly when $x$ is a root of the $\ell$-th division polynomial. It is the dictionary used in the construction and comparison of Drinfeld level structures, and is invoked by the statements relating Weil pairings, determinants and relabellings of full-level and $\Gamma_0$-type level data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_iff_eval_prePsi_eq_zero_of_isSectionThrough.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_KatzLevelP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

theorem WeierstrassCurve.DrinfeldGlobal.nsmul_eq_one_iff_eval_prePsi_eq_zero_of_isSectionThrough
    {A : Type} [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (T : Type) [CommRing T] [Algebra A T] (hℓT : IsUnit ((ℓ : ℕ) : T))
    (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ)
    (S : Section W) (x y : T) (hS : IsSectionThrough S x y) :
    (𝒢 T W hΔ).nsmul (𝟙 _) ℓ S = (𝒢 T W hΔ).one (𝟙 _) ↔ (W.preΨ ℓ).eval x = 0 := by sorry
