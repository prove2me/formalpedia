-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_variableChange_map_fstHom_eq_one_and_smul_eq_of_iso_of_projMap_comp_eq
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_variableChange_map_fstHom_eq_one_and_smul_eq_of_iso_of_projMap_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/5e99e9a8-43ad-5f53-a5c2-b8ab9c93c6bc
-- title:
--   Isomorphisms over k[ε] trivial mod ε come from variable changes
-- statement:
--   Let $k$ be a field and write $\pi$ for the ring homomorphism underlying `TrivSqZeroExt.fstHom k k k`, i.e. reduction $k[\varepsilon]\to k$ of the dual numbers. Let $W,W'$ be Weierstrass curves over $k[\varepsilon]$ with $\Delta(W)$ a unit and with equal reductions, $W'$ mapped along $\pi$ equal to $W$ mapped along $\pi$. For a Weierstrass curve $V$ over a ring $R$, `projModelCR` is $\operatorname{Proj}$ of the quotient of $R[X_0,X_1,X_2]$ by the span of the homogeneous Weierstrass cubic of $V$, with its induced grading; `projModelStrCR` is its structure morphism to $\operatorname{Spec} R$, and `kwZeroSect` is the section at infinity, a morphism $\operatorname{Spec} R\to$ `projModelCR` splitting that structure morphism. Assume given an isomorphism $\Psi$ between the projective models of $W$ and $W'$ such that $\Psi$ followed by the structure morphism of $W'$ is the structure morphism of $W$, and such that the zero section of $W$ followed by $\Psi$ is the zero section of $W'$. Assume moreover that there exist graded ring homomorphisms $\varphi$, $\varphi'$ from the homogeneous coordinate rings of $W$, $W'$ to those of their reductions along $\pi$, each pulling back the irrelevant ideal so that $\operatorname{Proj}$ is functorial on them, each a coefficient homomorphism (sending the class of a constant $a$ to the class of $\pi(a)$ and fixing each $X_i$), and making the square commute: `Proj.map φ hφ` followed by $\Psi$ equals the transport along the equality of reductions followed by `Proj.map φ' hφ'`. Then there is a Weierstrass variable change $C$ over $k[\varepsilon]$ whose reduction along $\pi$ is the identity variable change and with $C\cdot W=W'$.
--
--   This is the first-order (dual numbers) rigidity statement behind the classical fact that an isomorphism of pointed projective Weierstrass models is induced by a variable change $(x,y)\mapsto(u^2x+r,\;u^3y+su^2x+t)$: here the isomorphism is additionally assumed to be the identity on the special fibre, which forces $(u,r,s,t)\equiv(1,0,0,0)$ modulo $\varepsilon$. It feeds the deformation-theoretic comparison of Weierstrass models used further on in the construction of moduli of Weierstrass curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_variableChange_map_fstHom_eq_one_and_smul_eq_of_iso_of_projMap_comp_eq.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_variableChange_map_fstHom_eq_one_and_smul_eq_of_iso_of_projMap_comp_eq
    (k : Type) [Field k]
    (W W' : WeierstrassCurve (DualNumber k)) (hΔ : IsUnit W.Δ)
    (hW' : W'.map (TrivSqZeroExt.fstHom k k k).toRingHom = W.map (TrivSqZeroExt.fstHom k k k).toRingHom)
    (Ψ : projModelCR W.toProjective ≅ projModelCR W'.toProjective)
    (hΨ : Ψ.hom ≫ projModelStrCR W'.toProjective = projModelStrCR W.toProjective)
    (hΨO : (kwZeroSect (DualNumber k) W).1 ≫ Ψ.hom = (kwZeroSect (DualNumber k) W').1)
    (hΨred : ∃ (φ : projModelGradingCR W.toProjective →+*ᵍ
          projModelGradingCR (W.map (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective)
        (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ)
        (φ' : projModelGradingCR W'.toProjective →+*ᵍ
          projModelGradingCR (W'.map (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective)
        (hφ' : HomogeneousIdeal.irrelevant (projModelGradingCR (W'.map (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W'.toProjective)).map φ'),
        IsCoefficientHom W.toProjective (TrivSqZeroExt.fstHom k k k).toRingHom φ ∧
        IsCoefficientHom W'.toProjective (TrivSqZeroExt.fstHom k k k).toRingHom φ' ∧
        Proj.map φ hφ ≫ Ψ.hom =
          eqToHom (congrArg projModelCR (congrArg WeierstrassCurve.toProjective hW')).symm ≫
            Proj.map φ' hφ') :
    ∃ C : WeierstrassCurve.VariableChange (DualNumber k),
      C.map (TrivSqZeroExt.fstHom k k k).toRingHom = 1 ∧ C • W = W' := by sorry
