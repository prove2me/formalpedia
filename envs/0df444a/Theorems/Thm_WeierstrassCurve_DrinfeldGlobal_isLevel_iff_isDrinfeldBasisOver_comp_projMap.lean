-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isLevel_iff_isDrinfeldBasisOver_comp_projMap
-- name    : WeierstrassCurve.DrinfeldGlobal.isLevel_iff_isDrinfeldBasisOver_comp_projMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/29ff873a-1f52-5a2e-bfcb-6db6e443eb36
-- title:
--   Level structures transport to relative Drinfeld bases
-- statement:
--   Fix a commutative ring $A$, a prime $q$, and a family $\mathcal G$ of relative group laws assigning to every $A$-algebra $T$ and every projective Weierstrass curve $V$ over $T$ with unit discriminant a relative group law on the structure morphism `projModelStrCR V` of the graded Proj model; assume $\mathcal G$ satisfies `IsOriginIdentity`, i.e. for each such $T,V$ there is a ring homomorphism from the origin chart ring to $T$ which is a section of the identity of the group law and kills both `xOverY` and `zOverY`. Let $B$ be an $A$-algebra, $W$ a projective Weierstrass curve over $B$ with $\Delta(W)$ a unit, $T$ an $A$-algebra and $\varphi : B \to T$ an $A$-algebra map. Let $\varphi_c$ be a graded ring homomorphism from the Proj grading of $W$ to that of $W$ mapped along $\varphi$, such that the irrelevant ideal of the target is contained in the image of the irrelevant ideal, such that $\varphi_c$ sends the class of a constant $C\,a$ to $C\,\varphi(a)$ and each class of $X_i$ to $X_i$, and such that `Proj.map` $\varphi_c$ followed by `projModelStrCR W` equals `projModelStrCR (W.map φ)` followed by `Spec.map φ`. Let $x$ be a raw Drinfeld pair over $T$ (a curve together with two sections of its Proj model over the base) with $x.\mathrm{curve} = W$ mapped along $\varphi$, and suppose the two sections, transported by the identification of Proj models and then by `Proj.map` $\varphi_c$, both lie over `Spec.map φ` (hypotheses `hP`, `hQ`). Then $x$ is a level structure for the mapped curve — namely $x.\mathrm{curve}$ equals it and, for some witness that $\Delta(x.\mathrm{curve})$ is a unit, the basis divisor of $\mathcal G$ at $q$ for $x.P, x.Q$ equals the $q$-torsion ideal — if and only if the transported pair is a Drinfeld basis over `Spec.map φ` for the group law $\mathcal G\,B\,W$, i.e. the relative basis divisor at $q$ over `Spec.map φ` equals the relative $q$-torsion ideal over `Spec.map φ`.
--
--   This is the comparison dictionary between the absolute notion of a Drinfeld level structure on a member of the family over $T$ and the relative notion over the base $\operatorname{Spec} B$ pulled back along $\varphi$, in the style of Katz–Mazur's treatment of level structures and base change. It is what the representability arguments for the level moduli packages invoke when transporting level data along an algebra homomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_isLevel_iff_isDrinfeldBasisOver_comp_projMap.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.isLevel_iff_isDrinfeldBasisOver_comp_projMap
    {A : Type u} [CommRing A] (q : ℕ) [Fact q.Prime]
    (𝒢 : GroupLaws A) (h𝒢O : 𝒢.IsOriginIdentity)
    (B : Type u) [CommRing B] [Algebra A B] (W : WeierstrassCurve.Projective B) (hΔ : IsUnit W.Δ)
    (T : Type u) [CommRing T] [Algebra A T] (φ : B →ₐ[A] T)
    (φc : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map φ.toRingHom))
    (hφc : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map φ.toRingHom)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φc)
    (hcoef : IsCoefficientHom W φ.toRingHom φc)
    (hsq : Proj.map φc hφc ≫ projModelStrCR W =
      projModelStrCR (W.map φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))
    (x : RawDrinfeldPair T) (hc : x.curve = W.map φ.toRingHom)
    (hP : (x.P.1 ≫ eqToHom (congrArg projModelCR hc) ≫ Proj.map φc hφc) ≫ projModelStrCR W =
      Spec.map (CommRingCat.ofHom φ.toRingHom))
    (hQ : (x.Q.1 ≫ eqToHom (congrArg projModelCR hc) ≫ Proj.map φc hφc) ≫ projModelStrCR W =
      Spec.map (CommRingCat.ofHom φ.toRingHom)) :
    RawDrinfeldPair.IsLevel 𝒢 q (W.map φ.toRingHom) x ↔
      (𝒢 B W hΔ).IsDrinfeldBasisOver q (Spec.map (CommRingCat.ofHom φ.toRingHom))
        ⟨x.P.1 ≫ eqToHom (congrArg projModelCR hc) ≫ Proj.map φc hφc, hP⟩
        ⟨x.Q.1 ≫ eqToHom (congrArg projModelCR hc) ≫ Proj.map φc hφc, hQ⟩ := by sorry
