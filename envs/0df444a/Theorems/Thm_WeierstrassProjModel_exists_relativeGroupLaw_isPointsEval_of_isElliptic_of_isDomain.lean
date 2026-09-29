-- Prove2me | Theorems.Thm_WeierstrassProjModel_exists_relativeGroupLaw_isPointsEval_of_isElliptic_of_isDomain
-- name    : WeierstrassProjModel.exists_relativeGroupLaw_isPointsEval_of_isElliptic_of_isDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/4cff1f4c-d0b0-591f-94ad-95093e92e8ab
-- title:
--   Relative group law and points evaluation on elliptic Weierstrass Proj models
-- statement:
--   Let $R$ be a commutative ring which is a Noetherian integral domain, and let $V$ be a projective Weierstrass curve over $R$ whose associated affine Weierstrass curve is elliptic. Write $\pi =$ `projModelStrCR V` for the structure morphism of the Proj of the quotient grading `projModelGradingCR V`, namely `Proj.toSpecZero` followed by $\mathrm{Spec}$ of the algebra map from $R$ into the degree-zero part. The assertion is that the following data exist simultaneously. First, for every field $K$ carrying an $R$-algebra structure, the type of isomorphisms between the pullback of $\pi$ along $\mathrm{Spec}(R\to K)$ and `projModelCR (V.baseChange K)` is nonempty. Second, a `RelativeGroupLaw` $G$ for $\pi$: for every scheme $T$ and every morphism $t\colon T\to\mathrm{Spec}\,R$, operations `mul`, `one`, `inv` on the set of $\varphi\colon T\to\mathrm{Proj}$ with $\varphi$ followed by $\pi$ equal to $t$, satisfying associativity, both unit laws and left inverse cancellation, together with compatibility of `mul` with precomposition by any $\psi\colon T'\to T$ with $\psi$ followed by $t$ equal to $t'$. Third, for every field $F$ with an $R$-algebra structure, a bijection $\mathrm{ev}_F$ from the sections of $\pi$ over $\mathrm{Spec}(R\to F)$ to the Mathlib point group of $(V.\mathrm{baseChange}\,F).\mathrm{toAffine}$, such that `IsPointsEval V G ev` holds: $\mathrm{ev}_F$ sends $G.\mathrm{mul}$ to addition of points, and commutes with twisting by any $\sigma\in\mathrm{Aut}_R(F)$ (precomposition with $\mathrm{Spec}\,\sigma$ on one side, `Point.map` of $\sigma$ on the other).
--
--   This packages the group law on the projective Weierstrass model of an elliptic curve over a Noetherian domain, in a form valid in every residue characteristic and with no invertibility hypothesis on $2$: a functorial group structure on sections of the model together with its identification, field by field and Galois-equivariantly, with the usual chord-and-tangent group of affine points. It is the input used in the Čerednik–Drinfel'd quaternionic-model developments that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_exists_relativeGroupLaw_isPointsEval_of_isElliptic_of_isDomain.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.exists_relativeGroupLaw_isPointsEval_of_isElliptic_of_isDomain
    {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
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
