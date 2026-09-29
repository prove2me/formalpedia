-- Prove2me | Theorems.Thm_WeierstrassProjModel_exists_ringEquiv_zChartRing_of_iso_of_kwZeroSect_comp_eq
-- name    : WeierstrassProjModel.exists_ringEquiv_zChartRing_of_iso_of_kwZeroSect_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/81cdd9df-4840-517a-aecb-1502574bfc72
-- title:
--   Zero-preserving isomorphism of projective models restricts to Z-charts
-- statement:
--   Let $T$ be a commutative ring and let $W, W'$ be Weierstrass curves over $T$. For a Weierstrass cubic $V$ write $\mathrm{Proj}$ of the graded ring $\mathbb{Z}$-quotient $\mathrm{MvPolynomial}\,(\mathrm{Fin}\,3)\,T/(V.\mathrm{polynomial})$, graded by the images of the homogeneous components, for the projective model `projModelCR`, and `projModelStrCR` for its structure morphism to $\operatorname{Spec} T$, namely `Proj.toSpecZero` followed by $\operatorname{Spec}$ of $T \to (\text{degree-}0\text{ part})$. Assume given an isomorphism $\Psi$ of schemes from the projective model of $W$ to that of $W'$ such that $\Psi.\mathrm{hom}$ followed by the structure morphism of the model of $W'$ equals that of $W$ (so $\Psi$ is an isomorphism over $\operatorname{Spec} T$), and such that the underlying morphism of the zero section `kwZeroSect T W` followed by $\Psi.\mathrm{hom}$ equals the underlying morphism of `kwZeroSect T W'` (here the zero section of $W$ is $\operatorname{Spec}$ of the evaluation `kwYChartEval` followed by the affine chart inclusion `Proj.awayι` at the class of $X_1$). Then there exists a ring isomorphism $e$ from `ZChartRing W'.toProjective` to `ZChartRing W.toProjective`, i.e. between the degree-zero homogeneous localisations away from the class of $X_2$, such that: for every $t : T$, $e$ carries the image of $t$ in the $Z$-chart ring of $W'$, formed via `algebraMap` into the degree-zero part followed by `fromZeroRingHom`, to the corresponding image of $t$ for $W$; and $\operatorname{Spec}(e)$ followed by the chart morphism `zChartι W'.toProjective` equals `zChartι W.toProjective` followed by $\Psi.\mathrm{hom}$.
--
--   This is the statement that an isomorphism of projective Weierstrass models over $\operatorname{Spec} T$ matching the zero sections restricts to an isomorphism of the complementary affine charts $D_+(Z)$, compatibly with their $T$-algebra structures. It is the chart-restriction step used in showing that such an isomorphism over an Artinian base is induced by a Weierstrass variable change, as in [`WeierstrassProjModel.exists_variableChange_smul_eq_and_projMap_eq_inv_of_iso_of_kwZeroSect_comp_eq_of_isArtinianRing`](thm.html#WeierstrassProjModel.exists_variableChange_smul_eq_and_projMap_eq_inv_of_iso_of_kwZeroSect_comp_eq_of_isArtinianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_exists_ringEquiv_zChartRing_of_iso_of_kwZeroSect_comp_eq.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassProjModel.exists_ringEquiv_zChartRing_of_iso_of_kwZeroSect_comp_eq
    (T : Type) [CommRing T] (W W' : WeierstrassCurve T)
    (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1) :
    ∃ e : ZChartRing W'.toProjective ≃+* ZChartRing W.toProjective,
      (∀ t : T, e (fromZeroRingHom (projModelGradingCR W'.toProjective) _ (algebraMap T ((projModelGradingCR W'.toProjective) 0) t)) =
        fromZeroRingHom (projModelGradingCR W.toProjective) _ (algebraMap T ((projModelGradingCR W.toProjective) 0) t)) ∧
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ zChartι W'.toProjective = zChartι W.toProjective ≫ Ψ.hom := by sorry
