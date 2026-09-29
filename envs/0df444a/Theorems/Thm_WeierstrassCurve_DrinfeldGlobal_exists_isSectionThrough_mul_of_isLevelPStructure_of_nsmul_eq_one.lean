-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_isSectionThrough_mul_of_isLevelPStructure_of_nsmul_eq_one
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_isSectionThrough_mul_of_isLevelPStructure_of_nsmul_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/798ad54a-8ecc-5748-b425-bce14e8b3dda
-- title:
--   Sum of a level-ℓ section and q-torsion meets the affine chart
-- statement:
--   Let $A$ be a commutative ring and let $\mathcal G$ be a family of group laws over $A$, assigning to every commutative $A$-algebra $T$, every projective Weierstrass curve $W$ over $T$ and every proof that $\Delta_W$ is a unit a relative group law on the projective model of $W$. Assume $\mathcal G$ is chord–tangent, i.e. each member admits a points-evaluation `ev` satisfying `IsPointsEval`, and that its identity is the origin, i.e. the unit section $(\mathcal G\,T\,W\,h_\Delta).\mathrm{one}$ admits an origin-chart ring homomorphism $\chi$ with $\chi(xOverY)=\chi(zOverY)=0$. Let $\ell$ and $q$ be primes with $3\le\ell$ and $\ell\ne q$, let $T$ be a commutative $A$-algebra in which $\ell$ is a unit, and let $W$ be a projective Weierstrass curve over $T$ with $\Delta_W$ a unit. Let $D=(x_P,y_P,x_Q,y_Q)$ be level-$p$ data over $T$ which is a level-$\ell$ structure on $W$: both $(x_P,y_P)$ and $(x_Q,y_Q)$ satisfy the affine Weierstrass equation, the polynomial $W.\mathrm{pre}\Psi\,\ell$ vanishes at $x_P$ and at $x_Q$, and both products $\prod_{a=1}^{(\ell-1)/2}\bigl(x\,(W.\Psi\mathrm{Sq}\,a)(x_0)-(W.\Phi\,a)(x_0)\bigr)$, for $(x_0,x)=(x_P,x_Q)$ and $(x_Q,x_P)$, are units. Let $S$ be a section of the projective model which passes through $(x_P,y_P)$, in the sense that there is a ring homomorphism from the $Z$-chart ring of $W$ to $T$ realising $S$ as a $Z$-chart section with affine coordinates $x_P$ and $y_P$, and let $P$ be a section whose $q$-fold iterated sum under $\mathcal G\,T\,W\,h_\Delta$ is the unit section. Then there exist $x,y\in T$ such that the product of $S$ and $P$ under this group law is a section through $(x,y)$.
--
--   The statement records that adding a $q$-torsion section to a section through one of the two points of a Katz level-$\ell$ structure ($\ell\neq q$) yields a section that still lies in the affine chart $Z\neq 0$, so that it has affine coordinates over the base ring; the level-$\ell$ structure in the sense of Katz–Mazur forces the summand $S$ to have exact order $\ell$ in every residue field. It is used in the construction of level automorphisms in the full-level auxiliary theory.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_isSectionThrough_mul_of_isLevelPStructure_of_nsmul_eq_one.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

theorem WeierstrassCurve.DrinfeldGlobal.exists_isSectionThrough_mul_of_isLevelPStructure_of_nsmul_eq_one
    {A : Type} [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (q : ℕ) [Fact q.Prime] (hℓq : ℓ ≠ q)
    (T : Type) [CommRing T] [Algebra A T] (hℓT : IsUnit ((ℓ : ℕ) : T))
    (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ)
    (D : ModularCurve.LevelPData T) (hD : ModularCurve.IsLevelPStructure W ℓ D)
    (S : Section W) (hS : IsSectionThrough S D.xP D.yP)
    (P : Section W) (hP : (𝒢 T W hΔ).nsmul _ q P = (𝒢 T W hΔ).one _) :
    ∃ x y : T, IsSectionThrough ((𝒢 T W hΔ).mul _ S P) x y := by sorry
