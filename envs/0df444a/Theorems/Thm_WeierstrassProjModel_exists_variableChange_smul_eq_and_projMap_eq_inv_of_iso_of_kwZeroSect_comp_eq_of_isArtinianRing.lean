-- Prove2me | Theorems.Thm_WeierstrassProjModel_exists_variableChange_smul_eq_and_projMap_eq_inv_of_iso_of_kwZeroSect_comp_eq_of_isArtinianRing
-- name    : WeierstrassProjModel.exists_variableChange_smul_eq_and_projMap_eq_inv_of_iso_of_kwZeroSect_comp_eq_of_isArtinianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/a32dafd9-6ac2-5c16-802d-32f38247477b
-- title:
--   Origin-preserving isomorphisms of Weierstrass models are variable changes
-- statement:
--   Let $T$ be a commutative ring that is local and Artinian, and let $W,W'$ be Weierstrass curves over $T$ whose discriminants $W.\Delta$ and $W'.\Delta$ are units. Write $\mathrm{Proj}$ of the grading induced on $\mathrm{MvPolynomial}(\mathrm{Fin}\,3,T)/(\,\text{Weierstrass cubic}\,)$ by the homogeneous submodules for the projective model `projModelCR` of a Weierstrass curve, with structure morphism `projModelStrCR` to $\mathrm{Spec}\,T$ obtained from `Proj.toSpecZero` followed by $\mathrm{Spec}$ of the algebra map $T \to$ degree-zero part. Suppose given an isomorphism $\Psi$ of schemes between the projective models of $W$ and of $W'$ which is a morphism over $\mathrm{Spec}\,T$ (that is, $\Psi.\mathrm{hom}$ followed by the structure morphism of the model of $W'$ is the structure morphism of the model of $W$), and which carries the origin to the origin, in the sense that the underlying morphism of the section `kwZeroSect T W` followed by $\Psi.\mathrm{hom}$ equals that of `kwZeroSect T W'`. Then there exist a variable change $C$ over $T$ with $C \bullet W = W'$, a graded ring homomorphism $\varphi$ from the grading of the model of $W$ to that of the model of $C \bullet W$ whose image of the irrelevant ideal contains the irrelevant ideal of the target, such that $\varphi$ realises $C$ on homogeneous coordinates, i.e. $\varphi$ fixes the classes of the constants $a \in T$, sends the class of $X_0$ to that of $u^2X_0 + rX_2$, the class of $X_1$ to that of $u^3X_1 + u^2sX_0 + tX_2$, and the class of $X_2$ to that of $X_2$; and moreover the canonical identification of the model of $W'$ with the model of $C \bullet W$ coming from $C \bullet W = W'$, followed by $\mathrm{Proj}.\mathrm{map}\,\varphi$, equals $\Psi.\mathrm{inv}$.
--
--   This is the rigidity statement that an isomorphism of pointed projective Weierstrass models over an Artinian local ring is induced by a Weierstrass variable change $(u,r,s,t)$, in the shape classically recorded in Silverman III.3.1(b) and Katz–Mazur; the conclusion also identifies the inverse isomorphism with the morphism of $\mathrm{Proj}$'s attached to the variable change. It feeds the global Drinfeld-level comparison [`WeierstrassCurve.DrinfeldGlobal.exists_variableChange_map_fstHom_eq_one_and_smul_eq_of_iso_of_projMap_comp_eq`](thm.html#WeierstrassCurve.DrinfeldGlobal.exists_variableChange_map_fstHom_eq_one_and_smul_eq_of_iso_of_projMap_comp_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_exists_variableChange_smul_eq_and_projMap_eq_inv_of_iso_of_kwZeroSect_comp_eq_of_isArtinianRing.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
attribute [local instance] MvPolynomial.gradedAlgebra
open IsLocalRing in

theorem WeierstrassProjModel.exists_variableChange_smul_eq_and_projMap_eq_inv_of_iso_of_kwZeroSect_comp_eq_of_isArtinianRing
    (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T]
    (W W' : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (hΔ' : IsUnit W'.Δ)
    (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect T W).1 ≫ Ψ.hom = (kwZeroSect T W').1) :
    ∃ (C : WeierstrassCurve.VariableChange T) (hC : C • W = W')
      (φ : projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR (C • W).toProjective)
      (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W).toProjective) ≤
        (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ),
      IsVariableChangeHom W.toProjective C φ ∧
      eqToHom (congrArg projModelCR (congrArg WeierstrassCurve.toProjective hC)).symm ≫ Proj.map φ hφ = Ψ.inv := by sorry
