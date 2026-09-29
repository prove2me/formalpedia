-- Prove2me | Theorems.Thm_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso
-- name    : WeierstrassProjModel.kw_hgi_geometricallyIntegral_of_baseChangeIso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/5df5a4f9-8177-5bbe-aeaa-fe2bbeb63408
-- title:
--   Geometric integrality of the projective Weierstrass model
-- statement:
--   Let $R$ be a commutative ring and $W$ a Weierstrass curve over $R$, with associated projective Weierstrass data `W.toProjective`. For a projective Weierstrass curve $V$ over a commutative ring, `projModelCR V` denotes $\operatorname{Proj}$ of the graded ring `ProjModelRingCR V`, the quotient of the polynomial ring in three variables $\mathrm{MvPolynomial}\ (\mathrm{Fin}\ 3)$ by the homogeneous ideal `projModelHomogeneousIdealCR V`, graded by the images of the homogeneous components; `projModelStrCR V` is the structure morphism $\operatorname{Proj} \to \operatorname{Spec} R$ obtained as `Proj.toSpecZero` followed by the morphism of spectra induced by the algebra map from $R$ into the degree-zero part. The hypothesis `hbc` assumes that for every type $K$ in the same universe as $R$, equipped with a field structure and an $R$-algebra structure, there exists an isomorphism of schemes between the pullback of `projModelStrCR W.toProjective` along the morphism $\operatorname{Spec} K \to \operatorname{Spec} R$ induced by the algebra map $R \to K$, and `projModelCR` of the base change `W.toProjective.baseChange K`. The conclusion is that the morphism `projModelStrCR W.toProjective` is geometrically integral, i.e. for every field $K$ which is an $R$-algebra the corresponding pullback is an integral scheme.
--
--   This records that the projective Weierstrass model of a Weierstrass curve over an arbitrary base ring has integral geometric fibres, conditionally on the expected identification of its base changes with the projective models of the base-changed curves. It is used widely downstream in the construction and analysis of models of elliptic curves and of quaternionic uniformisation data, where integrality of fibres is a standing hypothesis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_kw_hgi_geometricallyIntegral_of_baseChangeIso.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Mathlib.AlgebraicGeometry.Geometrically.Integral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.kw_hgi_geometricallyIntegral_of_baseChangeIso.{u} {R : Type u}
    [CommRing R] (W : WeierstrassCurve R)
    (hbc : ∀ (K : Type u) [Field K] [Algebra R K],
      Nonempty (pullback (projModelStrCR W.toProjective)
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))
        ≅ projModelCR (W.toProjective.baseChange K))) :
    GeometricallyIntegral (projModelStrCR W.toProjective) := by sorry
