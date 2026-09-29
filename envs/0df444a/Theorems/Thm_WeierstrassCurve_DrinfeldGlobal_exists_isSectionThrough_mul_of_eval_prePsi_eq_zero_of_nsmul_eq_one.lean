-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_isSectionThrough_mul_of_eval_prePsi_eq_zero_of_nsmul_eq_one
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_isSectionThrough_mul_of_eval_prePsi_eq_zero_of_nsmul_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/c12daa91-c5e7-52a7-aa48-7ad09bb7e1ff
-- title:
--   Sum of an ℓ-division point and a q-torsion section is affine
-- statement:
--   Let $A$ be a commutative ring and let $\mathcal{G}$ be a family of group laws over $A$: for every $A$-algebra $T$ and every projective Weierstrass curve $W$ over $T$ whose discriminant $W.\Delta$ is a unit, a relative group law on the projective Weierstrass model of $W$ over $\operatorname{Spec} T$. Assume $\mathcal{G}$ is chord–tangent, i.e. for each such $T$, $W$ and unit witness there is an identification $ev$ of sections with affine points satisfying `IsPointsEval`, and that $\mathcal{G}$ has the origin as identity, i.e. for each such datum there is a ring homomorphism $\chi$ from the origin-chart ring of $W$ to $T$ which is an origin-chart section of $\mathcal{G}$'s unit section and kills both $xOverY$ and $zOverY$. Let $\ell$ and $q$ be primes with $3 \le \ell$ and $\ell \ne q$, let $T$ be a commutative $A$-algebra in which $\ell$ is invertible, and let $W$ be a projective Weierstrass curve over $T$ with $W.\Delta$ a unit. Let $S$ be a section of the projective model over $\operatorname{Spec} T$ passing through the affine coordinates $x, y \in T$, in the sense that some ring homomorphism from the $Z$-chart ring of $W$ to $T$ is a $Z$-chart section of $S$ with affine coordinate functions $x$ and $y$, and suppose $(W.\mathrm{pre}\Psi\,\ell)$ vanishes at $x$. Let $P$ be a section with $q \cdot P =$ the unit section, where $q \cdot P$ is the $q$-fold iterate of multiplication by $P$ applied to the unit section. Then there exist $x', y' \in T$ such that the product $S \cdot P$ formed with $\mathcal{G}_T(W)$ again passes through the affine coordinates $(x', y')$.
--
--   This is the affineness statement needed to add a $q$-torsion section to a point of exact order $\ell$ without leaving the affine chart $D_+(Z)$: since $\gcd(\ell, q) = 1$, the sum cannot specialise to the origin in any residue field of $T$, so the resulting $T$-point factors through the $Z$-chart and acquires affine coordinates. It is used in the construction of auxiliary level structures on moduli of elliptic curves with full level structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_isSectionThrough_mul_of_eval_prePsi_eq_zero_of_nsmul_eq_one.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

theorem WeierstrassCurve.DrinfeldGlobal.exists_isSectionThrough_mul_of_eval_prePsi_eq_zero_of_nsmul_eq_one
    {A : Type} [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (q : ℕ) [Fact q.Prime] (hℓq : ℓ ≠ q)
    (T : Type) [CommRing T] [Algebra A T] (hℓT : IsUnit ((ℓ : ℕ) : T))
    (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ)
    (S : Section W) (x y : T) (hS : IsSectionThrough S x y) (hx : (W.preΨ ℓ).eval x = 0)
    (P : Section W) (hP : (𝒢 T W hΔ).nsmul _ q P = (𝒢 T W hΔ).one _) :
    ∃ x' y' : T, IsSectionThrough ((𝒢 T W hΔ).mul _ S P) x' y' := by sorry
