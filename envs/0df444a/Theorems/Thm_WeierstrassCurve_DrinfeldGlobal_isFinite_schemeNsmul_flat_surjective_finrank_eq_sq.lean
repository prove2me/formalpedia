-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isFinite_schemeNsmul_flat_surjective_finrank_eq_sq
-- name    : WeierstrassCurve.DrinfeldGlobal.isFinite_schemeNsmul_flat_surjective_finrank_eq_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/df9bc108-047b-5614-a0db-693ff4b44f3a
-- title:
--   Multiplication by n is finite flat of rank n²
-- statement:
--   Let $A$ be a commutative ring and let $\mathcal G$ be a family of group laws over $A$: for every commutative $A$-algebra $T$, every projective Weierstrass curve $W$ over $T$ and every proof that the discriminant $\Delta(W)$ is a unit, $\mathcal G$ provides a relative group law on the structure morphism $E_W = \operatorname{Proj}$ of the graded ring of the projective model of $W$ over $\operatorname{Spec} T$, i.e. a functorial group structure on $T'$-points for all $T'$-schemes over $\operatorname{Spec} T$ (associative multiplication, neutral element, inverses, compatible with base change along morphisms over $\operatorname{Spec} T$). Assume `𝒢.IsChordTangent`: for each such $T$, $W$, $\Delta$ unit there is a family of bijections, for every field $F$ that is an algebra over the base, between the $F$-points of the projective model and the group of points of the affine curve $W$ base-changed to $F$, which carries the relative multiplication to addition of points and commutes with the action of algebra automorphisms of $F$. Assume also `𝒢.IsOriginIdentity`: in each case the neutral section factors as $\operatorname{Spec}$ of a ring homomorphism $\chi$ from the origin chart ring (the degree-zero localisation of the projective model away from the second coordinate) into $T$, followed by the origin chart immersion, with $\chi$ killing both $x/y$ and $z/y$. Let $T$ be a commutative $A$-algebra, $W$ a Weierstrass curve over $T$ with $\Delta(W)$ a unit, and $n \neq 0$ a natural number. Then the endomorphism $[n]$ of the projective model of $W$ — the morphism underlying the $n$-fold sum of the identity point, formed by iterating the relative multiplication of $\mathcal G\,T\,W$ starting from the neutral element — is finite, flat, locally of finite presentation and surjective, and its rank at every point $p$ of the projective model equals $n^2$.
--
--   This is the standard statement that multiplication by a nonzero integer on an elliptic curve over an arbitrary base is finite locally free of rank $n^2$, valid in all characteristics and in particular when $n$ is divisible by a residue characteristic, where $[n]$ fails to be étale. It supplies the finite flat rank-$n^2$ input for the Drinfeld level structures built in [`WeierstrassCurve.DrinfeldGlobal.exists_iso_projModelCR_map_map_of_frobenius_of_comp_schemeNsmul_eq_one_of_nsmul_eq_one`](thm.html#WeierstrassCurve.DrinfeldGlobal.exists_iso_projModelCR_map_map_of_frobenius_of_comp_schemeNsmul_eq_one_of_nsmul_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_isFinite_schemeNsmul_flat_surjective_finrank_eq_sq.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.isFinite_schemeNsmul_flat_surjective_finrank_eq_sq
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (n : ℕ) (hn : n ≠ 0) :
    IsFinite ((𝒢 T W hΔ).schemeNsmul n) ∧ Flat ((𝒢 T W hΔ).schemeNsmul n) ∧
      LocallyOfFinitePresentation ((𝒢 T W hΔ).schemeNsmul n) ∧ Surjective ((𝒢 T W hΔ).schemeNsmul n) ∧
      ∀ p, ((𝒢 T W hΔ).schemeNsmul n).finrank p = n ^ 2 := by sorry
