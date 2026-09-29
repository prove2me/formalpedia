-- Prove2me | Theorems.Thm_WeierstrassProjModel_projModel_isPullback_baseChange_ring
-- name    : WeierstrassProjModel.projModel_isPullback_baseChange_ring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/5314a90a-c06b-50a3-ad64-6f36707ee795
-- title:
--   Base change of the projective Weierstrass model over a ring
-- statement:
--   Let $R$ be a commutative ring and let $V$ be a projective Weierstrass curve over $R$, i.e. a term of `WeierstrassCurve.Projective R`; let $K$ be a commutative ring equipped with an $R$-algebra structure (both $R$ and $K$ in the same universe). For such a $V$, `projModelCR V` is the scheme $\operatorname{Proj}$ of the graded ring obtained by equipping the quotient of the polynomial ring in three variables over $R$ by the homogeneous ideal `projModelHomogeneousIdealCR V` of the Weierstrass cubic with the induced grading (the images of the homogeneous submodules of `MvPolynomial (Fin 3) R`), and `projModelStrCR V` is its structure morphism to $\operatorname{Spec} R$, namely the canonical map $\operatorname{Proj} \to \operatorname{Spec}$ of the degree-zero part followed by $\operatorname{Spec}$ of the algebra map from $R$ into that degree-zero part. The assertion is that there exists a morphism of schemes $\alpha \colon$ `projModelCR (V.baseChange K)` $\to$ `projModelCR V` making the square with $\alpha$ on top, the two structure morphisms `projModelStrCR (V.baseChange K)` and `projModelStrCR V` as the vertical maps, and $\operatorname{Spec}$ of the algebra map $R \to K$ along the bottom, a pullback square; in particular that square commutes and exhibits the projective model of the base-changed curve $V_K$ as the fibre product of the projective model of $V$ with $\operatorname{Spec} K$ over $\operatorname{Spec} R$.
--
--   This is the compatibility of the $\operatorname{Proj}$ construction with base change, specialised to the projective plane model of a Weierstrass curve and stated for an arbitrary $R$-algebra $K$ rather than only for fields. It is used to identify global sections of the pullback of the structure morphism in [`WeierstrassProjModel.bijective_appTop_pullback_snd_projModelStrCR`](thm.html#WeierstrassProjModel.bijective_appTop_pullback_snd_projModelStrCR) and in the construction of the relative group law on an elliptic Weierstrass model via base-change isomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_projModel_isPullback_baseChange_ring.lean

import Definitions.Def_WeierstrassCurve_ProjModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

universe u

theorem WeierstrassProjModel.projModel_isPullback_baseChange_ring
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R)
    (K : Type u) [CommRing K] [Algebra R K] :
    ∃ (α : projModelCR (V.baseChange K) ⟶ projModelCR V),
      IsPullback α (projModelStrCR (V.baseChange K)) (projModelStrCR V)
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by sorry
