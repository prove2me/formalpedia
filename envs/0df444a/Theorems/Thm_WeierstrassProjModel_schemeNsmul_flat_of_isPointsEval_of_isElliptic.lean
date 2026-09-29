-- Prove2me | Theorems.Thm_WeierstrassProjModel_schemeNsmul_flat_of_isPointsEval_of_isElliptic
-- name    : WeierstrassProjModel.schemeNsmul_flat_of_isPointsEval_of_isElliptic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/c76c6bab-12c9-5964-9987-9907ade87ce4
-- title:
--   Flatness of multiplication by n on the projective Weierstrass model
-- statement:
--   Let $R$ be a commutative ring and let $V$ be a projective Weierstrass curve over $R$ whose associated affine curve is elliptic (its discriminant is a unit). Write $\pi_V \colon \operatorname{Proj}$ of the graded quotient of the polynomial ring in three variables by the homogeneous ideal of the Weierstrass cubic $\to \operatorname{Spec} R$ for the structure morphism `projModelStrCR V`. Let $G$ be a relative group law on $\pi_V$: for every scheme $T$ with a morphism $t \colon T \to \operatorname{Spec} R$ it provides a multiplication, unit and inversion on the set of $T$-points over $t$ (morphisms $T \to V_{\mathrm{proj}}$ whose composite with $\pi_V$ is $t$), satisfying associativity, the two unit laws and left inversion, the multiplication being natural in $(T,t)$. Let $\mathrm{ev}$ be a family of bijections, one for each field $F$ that is an $R$-algebra, from the $F$-points over $\operatorname{Spec}$ of $R \to F$ to the group of points of the affine curve $V \times_R F$, and assume the predicate `IsPointsEval`: each $\mathrm{ev}_F$ carries the group law $G$ to addition of points, and intertwines the twist of a point by an $R$-algebra automorphism $\sigma$ of $F$ with the induced map on points. Let $n \neq 0$ be a natural number. Then the endomorphism `G.schemeNsmul n` of $V_{\mathrm{proj}}$, namely the underlying morphism of the $n$-fold $G$-product of the identity point with itself, is flat.
--
--   This is the flatness of multiplication by $n$ on a projective Weierstrass model over an arbitrary base ring with invertible discriminant, in the form of a flat morphism of schemes. It feeds the study of the $n$-torsion subscheme and Drinfeld level structures, being used for the flatness of the kernel scheme, for the finiteness and degree $n^2$ statement, and for the construction of Drinfeld bases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_schemeNsmul_flat_of_isPointsEval_of_isElliptic.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel in

theorem WeierstrassProjModel.schemeNsmul_flat_of_isPointsEval_of_isElliptic
    {R : Type} [CommRing R] (V : WeierstrassCurve.Projective R) [V.toAffine.IsElliptic]
    (G : RelativeGroupLaw R (projModelStrCR V))
    (ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra R F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR V) ≃
        (V.baseChange F).toAffine.Point)
    (hev : IsPointsEval V G ev) (n : ℕ) (hn : n ≠ 0) :
    Flat (G.schemeNsmul n) := by sorry
