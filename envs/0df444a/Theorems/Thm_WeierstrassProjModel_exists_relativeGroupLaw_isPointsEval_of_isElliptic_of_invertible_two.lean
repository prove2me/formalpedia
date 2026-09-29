-- Prove2me | Theorems.Thm_WeierstrassProjModel_exists_relativeGroupLaw_isPointsEval_of_isElliptic_of_invertible_two
-- name    : WeierstrassProjModel.exists_relativeGroupLaw_isPointsEval_of_isElliptic_of_invertible_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/eef69447-1207-5cb2-a8e7-180ce520200a
-- title:
--   Relative group law and points evaluation on the projective Weierstrass model
-- statement:
--   Let $R$ be a Noetherian integral domain (in `Type`) in which $2$ is invertible, and let $V$ be a projective Weierstrass curve over $R$ whose associated affine Weierstrass curve is elliptic, i.e. has invertible discriminant. Then there exist, simultaneously: (i) a family $h_{\mathrm{bc}}$ assigning to every field $K$ that is an $R$-algebra a nonempty type of isomorphisms of schemes between the pullback of the structure morphism `projModelStrCR V` along $\operatorname{Spec}$ of $R \to K$ and the Proj model `projModelCR` of the base change $V_K$; (ii) a `RelativeGroupLaw` $G$ for `projModelStrCR V`, that is, an operation on the sets $\{\varphi : T \to \mathrm{Proj}\ \mid \varphi$ followed by the structure morphism equals $t\}$ of $T$-points over each $t : T \to \operatorname{Spec} R$, together with unit and inverse, satisfying associativity, left and right unit laws, left inverse cancellation, and naturality of the multiplication under precomposition with morphisms $\psi : T' \to T$ over $\operatorname{Spec} R$; (iii) for each field $F$ that is an $R$-algebra, a bijection $\mathrm{ev}_F$ from the $F$-points of `projModelStrCR V` over $\operatorname{Spec}$ of $R \to F$ to the group $(V_F).\mathrm{toAffine}.\mathrm{Point}$ of points of the base-changed affine Weierstrass curve, such that `IsPointsEval` holds: each $\mathrm{ev}_F$ sends $G$'s multiplication to addition of points, and commutes with the action of any $R$-algebra automorphism $\sigma$ of $F$, the action on scheme points being precomposition with $\operatorname{Spec}(\sigma)$ and on affine points being `Point.map`.
--
--   This packages the group structure of an elliptic curve over a base into the functor-of-points form on the plane Proj model, in the style of the complete systems of addition laws of Lange–Ruppert, with the comparison to the elementary chord-and-tangent group law on $F$-points. It is used in the construction of the Hopf-algebra description of $p$-power torsion of elliptic curves over $\mathbb{Q}$ and over $p$-adic fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_exists_relativeGroupLaw_isPointsEval_of_isElliptic_of_invertible_two.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.exists_relativeGroupLaw_isPointsEval_of_isElliptic_of_invertible_two
    {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Invertible (2 : R)]
    (V : WeierstrassCurve.Projective R) [V.toAffine.IsElliptic] :
    ∃ (hbc : ∀ (K : Type) [Field K] [Algebra R K],
        Nonempty (pullback (projModelStrCR V)
            (Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ≅ projModelCR (V.baseChange K)))
      (G : RelativeGroupLaw R (projModelStrCR V))
      (ev : ∀ (F : Type) [Field F] [DecidableEq F] [Algebra R F],
        SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR V) ≃
          (V.baseChange F).toAffine.Point),
      IsPointsEval V G ev := by sorry
