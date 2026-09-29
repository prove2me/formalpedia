-- Prove2me | Theorems.Thm_WeierstrassProjModel_flat_schemeKerStr_of_isPointsEval_of_isElliptic
-- name    : WeierstrassProjModel.flat_schemeKerStr_of_isPointsEval_of_isElliptic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/be620682-1864-514f-a7d4-d171e322d23c
-- title:
--   Flatness of the n-torsion scheme over the base
-- statement:
--   Let $R$ be a commutative ring and let $V$ be a projective Weierstrass curve over $R$ whose associated affine Weierstrass curve is elliptic (its discriminant is a unit). Let $G$ be a relative group law on the structure morphism `projModelStrCR V` from $\mathrm{Proj}$ of the graded quotient ring attached to the homogeneous Weierstrass ideal to $\operatorname{Spec} R$: that is, functorial operations `mul`, `one`, `inv` on the sets of $T$-points over $\operatorname{Spec} R$, satisfying associativity, the unit laws, left inverses, and naturality of `mul` under base change of the test scheme. Let `ev` be a family, indexed by fields $F$ that are $R$-algebras, of bijections between the $\operatorname{Spec} F$-points of the projective model over $\operatorname{Spec} R$ and the points of the affine curve $V_F$; assume `IsPointsEval V G ev`, i.e. each `ev F` carries `G.mul` to addition of points, and is equivariant for the twist of a point by an $R$-algebra automorphism $\sigma$ of $F$ and the induced map on affine points. Let $n \neq 0$ be a natural number. Then the morphism `G.schemeKerStr n`, the second projection to $\operatorname{Spec} R$ of the pullback of the endomorphism `G.schemeNsmul n` of the projective model (the $n$-fold $G$-sum of the identity point) along the unit section $\operatorname{Spec} R \to V$, is flat.
--
--   This is the flatness half of the statement that multiplication by $n$ on an elliptic curve is finite locally free, so that the $n$-torsion subscheme $V[n]$ is flat over the base (Katz–Mazur, Theorem 2.3.1). Combined with finiteness of the same morphism, it feeds the construction of a finite free $\mathbb{Z}_p$-Hopf algebra of rank $p^2$ representing the $p$-torsion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_flat_schemeKerStr_of_isPointsEval_of_isElliptic.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel in

theorem WeierstrassProjModel.flat_schemeKerStr_of_isPointsEval_of_isElliptic
    {R : Type} [CommRing R] (V : WeierstrassCurve.Projective R) [V.toAffine.IsElliptic]
    (G : RelativeGroupLaw R (projModelStrCR V))
    (ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra R F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR V) ≃
        (V.baseChange F).toAffine.Point)
    (hev : IsPointsEval V G ev) (n : ℕ) (hn : n ≠ 0) :
    Flat (G.schemeKerStr n) := by sorry
