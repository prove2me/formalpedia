-- Prove2me | Theorems.Thm_WeierstrassProjModel_bijective_appTop_pullback_snd_projModelStrCR
-- name    : WeierstrassProjModel.bijective_appTop_pullback_snd_projModelStrCR
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/d73a3fec-35eb-5116-9d71-a89cb9d9203f
-- title:
--   Global sections of the projective Weierstrass model after base change
-- statement:
--   Let $R$ be a commutative ring, let $V$ be a projective Weierstrass curve over $R$ (a `WeierstrassCurve.Projective R`), and let $S$ be a commutative ring equipped with an $R$-algebra structure. Write $\mathcal{A} =$ `projModelGradingCR V` for the grading on the quotient ring `ProjModelRingCR V` induced, via `quotGradingSubmodule`, by the standard grading of `MvPolynomial (Fin 3) R` into homogeneous submodules together with the homogeneous ideal `projModelHomogeneousIdealCR V`; the structure morphism `projModelStrCR V` $: \operatorname{Proj}\mathcal{A} \to \operatorname{Spec} R$ is `Proj.toSpecZero` followed by $\operatorname{Spec}$ of the algebra map $R \to \mathcal{A}_0$. Form the fibre product of this morphism with $\operatorname{Spec}$ of the structure map $R \to S$, and let `pullback.snd` be its second projection, a morphism to $\operatorname{Spec} S$. The assertion is that the induced ring homomorphism on global sections, from $\Gamma(\operatorname{Spec} S, \top)$ to the global sections of the fibre product, is bijective. In other words, the base change to $S$ of the projective Weierstrass model has exactly $S$ as its ring of global functions.
--
--   This is the $H^0$ base-change statement for the projective plane cubic model: the base-changed model has no global functions beyond the constants. It serves as the scheme-theoretic input to rigidity arguments over an arbitrary base, and is used in [`WeierstrassProjModel.eq_snd_comp_of_comp_eq_const_of_isElliptic`](thm.html#WeierstrassProjModel.eq_snd_comp_of_comp_eq_const_of_isElliptic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_bijective_appTop_pullback_snd_projModelStrCR.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassProjModel.bijective_appTop_pullback_snd_projModelStrCR
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R) (S : Type u) [CommRing S] [Algebra R S] :
    Function.Bijective
      (pullback.snd (projModelStrCR V) (Spec.map (CommRingCat.ofHom (algebraMap R S)))).appTop := by sorry
