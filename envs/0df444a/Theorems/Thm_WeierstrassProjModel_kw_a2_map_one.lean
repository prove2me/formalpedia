-- Prove2me | Theorems.Thm_WeierstrassProjModel_kw_a2_map_one
-- name    : WeierstrassProjModel.kw_a2_map_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/d9109b0f-b0c5-5615-a8c9-655c18279631
-- title:
--   Chart factorisations of the zero section give [0:1:0]
-- statement:
--   Let $R$ be a commutative ring, $W$ a Weierstrass curve over $R$, and $F$ a field equipped with an $R$-algebra structure; fix an index $k \in \{0,1,2\}$. Write $A = \mathrm{MvPolynomial}\,(\mathrm{Fin}\ 3)\,R / (W_{\mathrm{proj}}.\mathrm{polynomial})$ for the homogeneous coordinate ring of the projective model, graded by the images `projModelGradingCR` of the homogeneous submodules, and let $\mathcal{A}_k$ be the degree-zero homogeneous localisation `HomogeneousLocalization.Away` of this grading at the image of $X_k$ in $A$, an $R$-algebra via the structure map into degree $0$. Let $\psi_k : \mathcal{A}_k \to F$ be an $R$-algebra homomorphism. Assume `hfac`: the composite of $\mathrm{Spec}\,(\mathrm{algebraMap}\ R\ F) : \mathrm{Spec}\,F \to \mathrm{Spec}\,R$ followed by the underlying morphism of the zero section `kwZeroSect R W` (built from the $Y$-chart evaluation and the open immersion `Proj.awayι`) coincides with $\mathrm{Spec}\,\psi_k$ followed by the $k$-th chart inclusion of `projModelAffineOpenCoverCR`. Then the triple $\bigl(\psi_k(\mathrm{gen}\ k\ 0), \psi_k(\mathrm{gen}\ k\ 1), \psi_k(\mathrm{gen}\ k\ 2)\bigr)$, i.e. `kw_lrApt_chartEval W F k ψₖ`, represents the same class in `WeierstrassCurve.Projective.PointClass F` as $(0,1,0)$.
--
--   This is the chart-level form of the unit law for the projective Weierstrass model: whenever an $F$-point of the model obtained by base change along the zero section factors through an affine chart of the standard cover, its projective coordinates are those of the point at infinity $[0:1:0]$. It is used in the verification of the group-law identities for the addition morphism, in particular by [`WeierstrassProjModel.addMorphism_mul_zeroSect`](thm.html#WeierstrassProjModel.addMorphism_mul_zeroSect), [`WeierstrassProjModel.addMorphism_zeroSect_mul`](thm.html#WeierstrassProjModel.addMorphism_zeroSect_mul) and [`WeierstrassProjModel.addMorphism_negMor_mul`](thm.html#WeierstrassProjModel.addMorphism_negMor_mul); for $k \neq 1$ the factorisation hypothesis cannot be met, so the content lies in the case $k = 1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_kw_a2_map_one.lean

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra in

theorem WeierstrassProjModel.kw_a2_map_one.{u} {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (F : Type u) [Field F] [Algebra R F] (k : Fin 3)
    (ψₖ : HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X k : MvPolynomial (Fin 3) R)) →ₐ[R] F)
    (hfac : (kw_lrAptb_tF (R := R) F) ≫ (kwZeroSect R W).1
      = Spec.map (CommRingCat.ofHom ψₖ.toRingHom) ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f k) :
    (⟦kw_lrApt_chartEval W F k ψₖ⟧ : WeierstrassCurve.Projective.PointClass F)
      = ⟦![(0:F), 1, 0]⟧ := by sorry
