-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_of_isSectionThrough_of_torsion_basis
-- name    : WeierstrassCurve.DrinfeldGlobal.isDrinfeldBasis_of_isSectionThrough_of_torsion_basis
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/7cbb7ab4-237b-5b32-8450-86e4057c2e0c
-- title:
--   Sections through an independent q-torsion pair are a Drinfeld basis
-- statement:
--   Let $A$ be a commutative ring and let $\mathcal{G}$ be a family of relative group laws assigning, to every commutative $A$-algebra $T$, every projective Weierstrass curve $W$ over $T$ and every proof that the discriminant $W.\Delta$ is a unit, a relative group law on the projective model scheme `projModelStrCR W`. Assume $\mathcal{G}$ is chord-and-tangent, i.e. for all such data there exists a points-evaluation family `ev` satisfying `IsPointsEval W (𝒢 T W hΔ) ev`, and that its identity is the origin, i.e. for all such data there is a ring homomorphism $\chi$ from the origin chart ring of $W$ to $T$ which is an origin-chart section of the unit section $(\mathcal{G}\,T\,W\,h_\Delta).\mathrm{one}(\mathrm{id})$ and kills both $x/y$ and $z/y$. Now let $T$ be a field and an $A$-algebra, let $W$ be a projective Weierstrass curve over $T$ whose discriminant is a unit, and let $q$ be a natural number with $q \neq 0$ in $T$. Let $S, S'$ be sections of the projective model over the base $\operatorname{Spec} T$ (morphisms to `projModelStrCR W` composing with the structure morphism to the identity), and let $x, y, x', y' \in T$ be such that `IsSectionThrough S x y` and `IsSectionThrough S' x' y'` hold, that is: there are ring homomorphisms from the $z$-chart ring of $W$ to $T$ which are $z$-chart sections for $S$, resp. $S'$, whose affine coordinate values are $(x,y)$, resp. $(x',y')$. Write $P =$ `toPoint W x y` and $P' =$ `toPoint W x' y'` for the associated elements of the Mordell–Weil group $W.\mathrm{toAffine}.\mathrm{Point}$ (the point $(x,y)$ when it is nonsingular, and $0$ otherwise). Assume $qP = 0$, $qP' = 0$, and that for all natural numbers $a, b < q$ the relation $aP + bP' = 0$ forces $a = b = 0$. Then `IsDrinfeldBasis (𝒢 T W hΔ) q S S'` holds: the ideal sheaf data `basisDivisor (𝒢 T W hΔ) q S S'`, obtained as `prodKerGraph` of the tuple of the $q^2$ linear combinations $aS + bS'$, coincides with `torsionIdeal (𝒢 T W hΔ) q`, the kernel ideal sheaf data cut out by multiplication by $q$ over the unit section.
--
--   This is the criterion that an honest pair of independent $q$-torsion points, read off as sections of the projective model through given affine coordinates, constitutes a Drinfeld $\Gamma(q)$-basis in the sense of Katz–Mazur, the scheme-theoretic equality of the divisor of the $q^2$ combinations with the $q$-torsion subscheme. It is used to supply the level-structure component of full-level data on Tate curves, where the two sections are the transported torsion points of the Tate parametrisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_of_isSectionThrough_of_torsion_basis.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassProjModel ModularCurve.LevelRelabelling
open WeierstrassCurve.DrinfeldGlobal
open scoped Classical

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.isDrinfeldBasis_of_isSectionThrough_of_torsion_basis
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    {T : Type} [Field T] [Algebra A T] (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ)
    (q : ℕ) (hq : ((q : ℕ) : T) ≠ 0)
    (S S' : Section W) (x y x' y' : T)
    (hS : IsSectionThrough S x y) (hS' : IsSectionThrough S' x' y')
    (hP : (q : ℤ) • toPoint W x y = 0) (hP' : (q : ℤ) • toPoint W x' y' = 0)
    (hind : ∀ a b : ℕ, a < q → b < q →
      (a : ℤ) • toPoint W x y + (b : ℤ) • toPoint W x' y' = 0 → a = 0 ∧ b = 0) :
    IsDrinfeldBasis (𝒢 T W hΔ) q S S' := by sorry
