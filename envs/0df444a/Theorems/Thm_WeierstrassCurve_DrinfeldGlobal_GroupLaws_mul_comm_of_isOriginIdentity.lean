-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_GroupLaws_mul_comm_of_isOriginIdentity
-- name    : WeierstrassCurve.DrinfeldGlobal.GroupLaws.mul_comm_of_isOriginIdentity
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/fec2a742-8ae5-5ac9-b4c7-81beb6225669
-- title:
--   Commutativity of origin-pinned relative group laws on Weierstrass models
-- statement:
--   Let $A$ be a commutative ring and let $\mathcal G$ be an element of `GroupLaws A`, that is, an assignment to every commutative $A$-algebra $T$, every projective Weierstrass curve $W$ over $T$ and every proof that $\Delta(W)$ is a unit of $T$, of a relative group law on the projective model $\mathrm{Proj}$-scheme `projModelStrCR W` over $\operatorname{Spec} T$. Assume: (i) $\mathcal G$ is chord–tangent, i.e. for all such $T$, $W$ and $h\Delta$ there is an `ev` for which the predicate `IsPointsEval W (𝒢 T W hΔ) ev` holds; (ii) $\mathcal G$ has origin identity, i.e. for all such $T$, $W$, $h\Delta$ there is a ring homomorphism $\chi$ from `OriginChartRing W` to $T$ with `IsOriginChartSection` for the unit section $(\mathcal G\,T\,W\,h\Delta).\mathrm{one}$ and with $\chi(x/y)=\chi(z/y)=0$, so that the unit is the point at infinity; (iii) variable changes are realised on homogeneous coordinate rings: for every commutative $A$-algebra $T$, every projective Weierstrass curve $W$ over $T$ and every variable change $C$ over $T$ there is a graded ring homomorphism $\varphi$ from `projModelGradingCR W` to `projModelGradingCR (C • W)` whose image of the irrelevant ideal contains the irrelevant ideal of the target and which satisfies `IsVariableChangeHom`, namely $\varphi$ fixes the classes of constants, sends the class of $X_0$ to that of $u^2X_0+rX_2$, the class of $X_1$ to that of $u^3X_1+u^2sX_0+tX_2$, and the class of $X_2$ to that of $X_2$; (iv) coefficient maps are realised likewise: for $A$-algebra homomorphisms $f : T \to T'$ and $W$ over $T$ there is such a graded homomorphism to `projModelGradingCR (W.map f)` satisfying `IsCoefficientHom`, i.e. sending the class of a constant $a$ to the class of $f(a)$ and fixing the classes of $X_0,X_1,X_2$. Then for every commutative $A$-algebra $T$, every projective Weierstrass curve $W$ over $T$ with $\Delta(W)$ a unit, and all sections $x,y$ of the structure morphism `projModelStrCR W` over $\operatorname{Spec} T$, the multiplications agree: $\mathcal G\,T\,W\,h\Delta$ satisfies $x\cdot y = y\cdot x$.
--
--   This is the commutativity of the group scheme structure on an elliptic curve over an arbitrary commutative base, in the form needed for the family of group laws attached to projective Weierstrass models: no field, domain or Noetherian hypothesis on $T$ is imposed. It is used throughout the construction of level structures on modular curves, where the group law on a Weierstrass model must be known to be commutative before Drinfeld bases, diamond operators and determinant computations can be set up.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_GroupLaws_mul_comm_of_isOriginIdentity.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open WeierstrassCurve.DrinfeldGlobal
open WeierstrassProjModel

theorem WeierstrassCurve.DrinfeldGlobal.GroupLaws.mul_comm_of_isOriginIdentity
    {A : Type} [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ)
    (x y : Section W) :
    (𝒢 T W hΔ).mul _ x y = (𝒢 T W hΔ).mul _ y x := by sorry
