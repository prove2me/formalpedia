-- Prove2me | Theorems.Thm_WeierstrassProjModel_flat_schemeFibreEndo_schemeNsmul_of_isPointsEval_of_isElliptic
-- name    : WeierstrassProjModel.flat_schemeFibreEndo_schemeNsmul_of_isPointsEval_of_isElliptic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/5a416329-db42-554c-9e63-c607a67762c6
-- title:
--   Fibrewise flatness of multiplication by n on the Weierstrass model
-- statement:
--   Let $R$ be a commutative ring and let $V$ be a projective Weierstrass cubic over $R$ whose associated affine Weierstrass curve is elliptic (its discriminant a unit). Write $f =$ `projModelStrCR V` for the structure morphism $\operatorname{Proj}$ of the graded quotient ring of $V$, composed with the morphism induced by $R \to$ (degree-zero part), to $\operatorname{Spec} R$. Assume given: a `RelativeGroupLaw` $G$ for $f$, that is, for every scheme $T$ with a morphism $t \colon T \to \operatorname{Spec} R$ a multiplication, unit and inversion on the set of $T$-points $\{\varphi \colon T \to \operatorname{Proj} \mid \varphi$ followed by $f$ equals $t\}$, satisfying associativity, both unit laws and left inverse, with the multiplication natural in $T$ along morphisms $\psi$ over $\operatorname{Spec} R$; and, for every field $F$ that is an $R$-algebra, a bijection $\mathrm{ev}_F$ from the set of points of $f$ over $\operatorname{Spec}$ of the map $R \to F$ to the group of affine points of $V$ base changed to $F$, subject to the hypothesis `IsPointsEval`: each $\mathrm{ev}_F$ carries $G$'s multiplication to addition of points, and for every $R$-algebra automorphism $\sigma$ of $F$ it carries the twist of a point by $\sigma$ (precomposition with $\operatorname{Spec} \sigma$) to the image of $\mathrm{ev}_F$ under `Point.map` $\sigma$. Let $n$ be a nonzero natural number, and let $[n] =$ `G.schemeNsmul n` be the underlying morphism $\operatorname{Proj} \to \operatorname{Proj}$ of the $n$-fold $G$-multiple of the identity point, which lies over $\operatorname{Spec} R$. Then for every point $s$ of $\operatorname{Spec} R$ the induced endomorphism of the fibre — the unique morphism of $\operatorname{Proj} \times_{\operatorname{Spec} R} \operatorname{Spec} \kappa(s)$ whose first projection is the first projection followed by $[n]$ and whose second projection is the second projection — is flat.
--
--   This is the fibrewise half of the classical statement that multiplication by $n$ on a Weierstrass elliptic curve over a base is flat: on each fibre it is a nonconstant endomorphism of a smooth proper geometrically integral curve over a field, hence flat. It feeds the fibre criterion of flatness used to prove flatness of $[n]$ itself and of the $n$-torsion subscheme, and is cited by the flatness statement for `G.schemeNsmul n` and by the finiteness and flatness statement for the kernel scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_flat_schemeFibreEndo_schemeNsmul_of_isPointsEval_of_isElliptic.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_AlgebraicGeometry_SchemeFibreEndo

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

universe u

theorem WeierstrassProjModel.flat_schemeFibreEndo_schemeNsmul_of_isPointsEval_of_isElliptic
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R) [V.toAffine.IsElliptic]
    (G : RelativeGroupLaw R (projModelStrCR V))
    (ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR V) ≃
        (V.baseChange F).toAffine.Point)
    (hev : IsPointsEval V G ev) (n : ℕ) (hn : n ≠ 0) (s : Spec (CommRingCat.of R)) :
    Flat (schemeFibreEndo (projModelStrCR V) (G.schemeNsmul n) (G.schemeNsmul_over n) s) := by sorry
