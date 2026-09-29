-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_isSectionThrough_zsmulSection_of_eval_prePsi_eq_zero
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_isSectionThrough_zsmulSection_of_eval_prePsi_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/06bc38a7-4ea6-51bf-b1f9-e28162226575
-- title:
--   Non-zero multiples of an ℓ-torsion section avoid infinity
-- statement:
--   Let $A$ be a commutative ring and let $\mathcal G$ be a family of relative group laws assigning, to every $A$-algebra $T$, every projective Weierstrass curve $W$ over $T$ and every proof that $W.\Delta$ is a unit, a group law on the functor of points of the projective model $\mathrm{projModelStrCR}\,W$ over $\operatorname{Spec} T$. Assume $\mathcal G$ is chord–tangent, i.e. for all such $T$, $W$ and $\Delta$-unit witness there is an $\mathrm{ev}$ with $\mathrm{IsPointsEval}\,W\,(\mathcal G\,T\,W\,h_\Delta)\,\mathrm{ev}$, and that it has origin identity, i.e. in each case the identity section admits a ring homomorphism $\chi$ from the origin chart ring to $T$ presenting it as an origin-chart section with $\chi(x/y)=\chi(z/y)=0$. Let $\ell$ be a prime with $\ell\ge 3$, let $T$ be a commutative $A$-algebra in which the image of $\ell$ is a unit, let $W$ be a projective Weierstrass curve over $T$ whose discriminant $\Delta$ is a unit, and let $S$ be a $T$-point of the projective model of $W$ which is a section through $(x,y)$, meaning that $S$ factors through the chart $\{Z\ne 0\}$ by a ring homomorphism $\chi$ from the $Z$-chart ring to $T$ with $\chi(X/Z)=x$ and $\chi(Y/Z)=y$. Assume the division polynomial $W.\mathrm{pre\Psi}\,\ell$ vanishes at $x$, and let $a$ be an integer not divisible by $\ell$. Then the $a$-fold multiple $\mathrm{zsmulSection}(\mathcal G\,T\,W\,h_\Delta)\,a\,S$ — the $a$-th iterate under the group law for $a\ge 0$, and the inverse of the $|a|$-th iterate otherwise — is again a section through some pair $(x',y')$ of elements of $T$.
--
--   This is the statement that a multiple by an integer prime to $\ell$ of an $\ell$-torsion section stays in the affine chart $Z\neq 0$, i.e. never meets the section at infinity, over an arbitrary base ring in which $\ell$ is invertible. It is the single-point analogue of the corresponding assertion for non-trivial combinations of a basis of the $\ell$-torsion, and it is what allows the scalar operations $P\mapsto[a]P$ on $\Gamma_1(\ell)$-structures to be given in affine coordinates over arbitrary test algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_isSectionThrough_zsmulSection_of_eval_prePsi_eq_zero.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

theorem WeierstrassCurve.DrinfeldGlobal.exists_isSectionThrough_zsmulSection_of_eval_prePsi_eq_zero
    {A : Type} [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (T : Type) [CommRing T] [Algebra A T] (hℓT : IsUnit ((ℓ : ℕ) : T))
    (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ)
    (S : Section W) (x y : T) (hS : IsSectionThrough S x y) (hx : (W.preΨ ℓ).eval x = 0)
    (a : ℤ) (ha : ¬ ((ℓ : ℤ) ∣ a)) :
    ∃ x' y' : T, IsSectionThrough (ModularCurve.LevelRelabelling.zsmulSection (𝒢 T W hΔ) a S) x' y' := by sorry
