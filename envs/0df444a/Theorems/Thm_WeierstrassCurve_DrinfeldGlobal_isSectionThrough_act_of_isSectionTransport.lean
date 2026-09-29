-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isSectionThrough_act_of_isSectionTransport
-- name    : WeierstrassCurve.DrinfeldGlobal.isSectionThrough_act_of_isSectionTransport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/03c33a20-f72f-54c2-a60b-e2844e69fac1
-- title:
--   Transport along a change of variables on sections through a point
-- statement:
--   Let $A$ be a commutative ring, $\mathcal{G}$ a family of relative group laws on the projective models of Weierstrass curves with unit discriminant over $A$-algebras, $q$ a natural number, and $\mathcal{T}$ a level transport datum for raw Drinfeld pairs over $A$ relative to $\mathcal{G}$ and $q$ (an assignment of pairs along $A$-algebra maps and along changes of variables, functorial and compatible with the level condition) satisfying `IsSectionTransport`. Let $T$ be a commutative $A$-algebra, $C=(u,r,s,t)$ a Weierstrass change of variables over $T$, and $x$ a raw Drinfeld pair over $T$, i.e. a projective Weierstrass curve `x.curve` together with two sections $P,Q$ of its projective model over the base. Assume `hVC`: there is a graded ring homomorphism $\varphi$ from the quotient grading of the projective model of `x.curve` to that of $C \bullet$ `x.curve`, carrying the irrelevant ideal of the target into the image of the irrelevant ideal of the source, which realises $C$ in the sense of `IsVariableChangeHom`: $\varphi$ fixes the classes of constants, sends the class of $X_0$ to that of $u^2X_0+rX_2$, the class of $X_1$ to that of $u^3X_1+u^2sX_0+tX_2$, and the class of $X_2$ to itself. Let $D$ be a quadruple $(x_P,y_P,x_Q,y_Q)$ of elements of $T$, and suppose $P$ passes through $(x_P,y_P)$ and $Q$ through $(x_Q,y_Q)$, where `IsSectionThrough S a b` means that there is a ring homomorphism $\chi$ from the $Z$-chart ring of the curve to $T$ which is a $Z$-chart section of $S$ with affine coordinates $\mathrm{affX}\,\chi=a$ and $\mathrm{affY}\,\chi=b$. Then the two sections of $\mathcal{T}.\mathrm{act}\,C\,x$ pass through the transformed data `D.variableChange C`, namely $P$ through $\bigl(u^{-2}(x_P-r),\,u^{-3}(y_P-s(x_P-r)-t)\bigr)$ and $Q$ through $\bigl(u^{-2}(x_Q-r),\,u^{-3}(y_Q-s(x_Q-r)-t)\bigr)$.
--
--   This is the compatibility, at the level of affine coordinates, between the action of an admissible change of variables on raw Drinfeld pairs and the classical substitution $x \mapsto u^{-2}(x-r)$, $y \mapsto u^{-3}(y-s(x-r)-t)$ on the points carrying the level structure. It is used in the construction and identification of automorphisms of the full-level moduli problem, including the level-one auxiliary computations on the Tate curve and the diamond operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_isSectionThrough_act_of_isSectionTransport.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal ModularCurve.LevelRelabelling
open scoped Classical

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.isSectionThrough_act_of_isSectionTransport
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (q : ℕ) (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    {T : Type} [CommRing T] [Algebra A T] (C : WeierstrassCurve.VariableChange T) (x : RawDrinfeldPair T)

    (hVC : ∃ (φ : projModelGradingCR x.curve →+*ᵍ projModelGradingCR (C • x.curve))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • x.curve)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR x.curve)).map φ),
        IsVariableChangeHom x.curve C φ)
    (D : ModularCurve.LevelPData T)
    (hP : IsSectionThrough x.P D.xP D.yP) (hQ : IsSectionThrough x.Q D.xQ D.yQ) :
    IsSectionThrough (𝒯.act C x).P (D.variableChange C).xP (D.variableChange C).yP ∧
      IsSectionThrough (𝒯.act C x).Q (D.variableChange C).xQ (D.variableChange C).yQ := by sorry
