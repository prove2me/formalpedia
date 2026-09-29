-- Prove2me | Theorems.Thm_WeierstrassProjModel_negMor_chartFactor
-- name    : WeierstrassProjModel.negMor_chartFactor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/d4636b38-0832-5fb0-928d-30b6f219afc8
-- title:
--   Negation morphism factors through the Z≠ 0 chart
-- statement:
--   Let $R$ be a commutative ring, $W$ a Weierstrass curve over $R$, and $F$ a field that is an $R$-algebra, all in one universe. Write $E = \mathrm{Proj}$ of the grading `projModelGradingCR W.toProjective`, the grading on $\mathrm{MvPolynomial}(\mathrm{Fin}\,3,R)/(W.\mathrm{toProjective}.\mathrm{polynomial})$ obtained as the image of the homogeneous submodules under the quotient map, and let $A$ be the homogeneous localisation away from the class of the third variable $X_2$, i.e. the coordinate ring of the chart $Z\neq 0$. The assertion is that there is an $R$-algebra endomorphism $\nu$ of $A$ with two properties. First, for every $R$-algebra map $\psi : A \to F$ and every pair $\varphi$ consisting of a morphism $\mathrm{Spec}\,F \to E$ together with a proof that it becomes, after composition with the structure morphism `projModelStrCR`, the morphism $\mathrm{Spec}$ of $\mathrm{algebraMap}\,R\,F$: if $\varphi$'s morphism is $\mathrm{Spec}(\psi)$ followed by the chart-$2$ immersion of `projModelAffineOpenCoverCR`, then $\varphi$'s morphism followed by the negation morphism `kw_lrAddNegDiag_negMor W` (the map of $\mathrm{Proj}$ induced by the negation graded homomorphism) is $\mathrm{Spec}(\psi\circ\nu)$ followed by that same chart immersion. Second, for every such $\psi$ the triple $k \mapsto (\psi\circ\nu)(\mathrm{gen}\,2\,k)$, $k \in \mathrm{Fin}\,3$, of chart-generator values equals the projective Weierstrass negation, for the base-changed curve $(W_F).\mathrm{toProjective}$, of the triple $k\mapsto\psi(\mathrm{gen}\,2\,k)$, which replaces the second coordinate $y$ by $-y-a_1x-a_3z$.
--
--   This is the chart-level description of negation on the projective Weierstrass model: on the affine chart $Z\neq 0$ the negation morphism of $\mathrm{Proj}$ is induced by an explicit $R$-algebra endomorphism of the chart ring, which on coordinates is the usual $(x,y,z)\mapsto(x,-y-a_1x-a_3z,z)$. It is used in the verification that the addition morphism composed with negation behaves as expected on points, in [`WeierstrassProjModel.addMorphism_negMor_mul`](thm.html#WeierstrassProjModel.addMorphism_negMor_mul) and [`WeierstrassProjModel.pin_addMorphism_negMor_mul`](thm.html#WeierstrassProjModel.pin_addMorphism_negMor_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_negMor_chartFactor.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry NeronModelInfra WeierstrassProjModel
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

theorem WeierstrassProjModel.negMor_chartFactor.{u} {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) (F : Type u) [Field F] [Algebra R F] :
    ∃ ν : (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) R)))
        →ₐ[R] (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) R))),
      (∀ (ψ : (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
            (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
              (MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) R))) →ₐ[R] F)
        (φ : SchemeHomOver (kw_lrAptb_tF (R := R) F) (projModelStrCR W.toProjective)),
        φ.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom)
            ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f (2 : Fin 3) →
        φ.1 ≫ kw_lrAddNegDiag_negMor W
          = Spec.map (CommRingCat.ofHom (ψ.comp ν).toRingHom)
            ≫ (projModelAffineOpenCoverCR R W.toProjective).openCover.f (2 : Fin 3))
      ∧ ∀ (ψ : (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
            (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
              (MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) R))) →ₐ[R] F),
        kw_lrApt_chartEval W F 2 (ψ.comp ν)
          = (kw_lrApt_WF W F).neg (kw_lrApt_chartEval W F 2 ψ) := by sorry
