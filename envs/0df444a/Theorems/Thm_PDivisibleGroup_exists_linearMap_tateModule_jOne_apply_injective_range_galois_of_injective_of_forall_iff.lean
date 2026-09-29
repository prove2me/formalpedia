-- Prove2me | Theorems.Thm_PDivisibleGroup_exists_linearMap_tateModule_jOne_apply_injective_range_galois_of_injective_of_forall_iff
-- name    : PDivisibleGroup.exists_linearMap_tateModule_jOne_apply_injective_range_galois_of_injective_of_forall_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/a398b6fd-5f09-581e-8c56-f3f8d49eb598
-- title:
--   Tate module map induced by an equivariant points dictionary
-- statement:
--   Let $p$ be a prime, $M$ a nonzero natural number, and $A$ a commutative ring equipped with an algebra structure over $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ`. Let $\mathcal G$ be a [`PDivisibleGroup A p h`](def/PDivisibleGroup_Basic.html#L199) of height $h$, that is, a system of finite free commutative cocommutative Hopf $A$-algebras `level v` of rank $p^{vh}$ with surjective transition maps whose kernels are the corresponding torsion ideals; write $\mathcal G(\overline{\mathbb Q})$ for `𝒢.Points`, the direct limit over $v$ of the additive groups attached to the level-$v$ points $\mathcal G_v(\overline{\mathbb Q}) =$ `𝒢.Point _ v`, and $J_1(Mp) =$ [`ModularCurve.JOne (M * p)`](def/ModularCurve_X1.html#L186), the group of degree-zero divisor classes of the function field `x1FunctionFieldBar (M * p)` over $\overline{\mathbb Q}$. Let $\Delta : \mathcal G(\overline{\mathbb Q}) \to J_1(Mp)$ be an additive homomorphism subject to three hypotheses: $\Delta$ is injective; for every $v$ and every $y \in J_1(Mp)$, the conditions $p^v\,y = 0$ and $y \in$ [`ModularCurve.normFreePartAt (M * p) p`](def/ModularCurve_X1PrimitiveSpecializationAtP.html#L29) (the range of `normFreeEnd` at the chosen representatives) hold if and only if $y = \Delta(x)$ for the image $x$ of some level-$v$ point under `𝒢.pointsMkAdd`; and for every $\tau \in \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ and every $A$-algebra automorphism $\tau'$ of $\overline{\mathbb Q}$ agreeing with $\tau$ pointwise, $\Delta(\tau' \cdot z) = \tau \cdot \Delta(z)$ for all $z$. Then there exists a $\mathbb Z_p$-linear map $e$ from [`TateModule p (𝒢.Points _)`](def/EllipticCurve_TateModule.html#L15) to [`TateModule p (JOne (M * p))`](def/EllipticCurve_TateModule.html#L15) — Tate modules being the groups of sequences $(x_n)$ with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$ — such that: $e$ is given levelwise by $(e x)_n = \Delta(x_n)$; $e$ is injective; a Tate module element $y$ lies in the range of $e$ precisely when every component $y_n$ lies in [`ModularCurve.normFreePartAt (M * p) p`](def/ModularCurve_X1PrimitiveSpecializationAtP.html#L29); and $e$ intertwines the actions, $e(\mathcal G.\mathrm{tateModuleRep}(\tau')\,x) = \mathrm{rep}(\tau)(e\,x)$ whenever $\tau'$ and $\tau$ agree pointwise on $\overline{\mathbb Q}$.
--
--   This transfers a levelwise dictionary between the points of a $p$-divisible group and the $p$-power torsion in the norm-free part of $J_1(Mp)$ into an injective, Galois-equivariant $\mathbb Z_p$-linear map of $p$-adic Tate modules with explicitly identified image. It is used in the analysis of $X_1(Mp)$ and its Jacobian at $p$, where the $p$-divisible group arising from good reduction data is compared with the $p$-adic representation on $T_p J_1(Mp)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_exists_linearMap_tateModule_jOne_apply_injective_range_galois_of_injective_of_forall_iff.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem PDivisibleGroup.exists_linearMap_tateModule_jOne_apply_injective_range_galois_of_injective_of_forall_iff
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (A : Type) [CommRing A] [Algebra A (AlgebraicClosure ℚ)]
    {h : ℕ} (𝒢 : PDivisibleGroup A p h)
    (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JOne (M * p))
    (hF1 : Function.Injective Δ)
    (hLEV : (∀ (v : ℕ) (y : ModularCurve.JOne (M * p)),
          ((p ^ v) • y = 0 ∧ y ∈ ModularCurve.normFreePartAt (M * p) p) ↔
          ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y))
    (hGAL : (∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[A] AlgebraicClosure ℚ),
          (∀ x : AlgebraicClosure ℚ, τ' x = τ x) → ∀ z : 𝒢.Points (AlgebraicClosure ℚ), Δ (τ' • z) = τ • Δ z)) :
    ∃ e : TateModule p (𝒢.Points (AlgebraicClosure ℚ)) →ₗ[ℤ_[p]] TateModule p (ModularCurve.JOne (M * p)),
      (∀ (x : TateModule p (𝒢.Points (AlgebraicClosure ℚ))) (n : ℕ),
        ((e x : TateModule p (ModularCurve.JOne (M * p))) : ℕ → ModularCurve.JOne (M * p)) n =
          Δ ((x : ℕ → 𝒢.Points (AlgebraicClosure ℚ)) n)) ∧
      Function.Injective e ∧
      (∀ y : TateModule p (ModularCurve.JOne (M * p)), y ∈ LinearMap.range e ↔
        ∀ n : ℕ, (y : ℕ → ModularCurve.JOne (M * p)) n ∈ ModularCurve.normFreePartAt (M * p) p) ∧
      (∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[A] AlgebraicClosure ℚ),
        (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
        ∀ x : TateModule p (𝒢.Points (AlgebraicClosure ℚ)),
          e (𝒢.tateModuleRep (AlgebraicClosure ℚ) τ' x) =
            TateModule.rep p (ModularCurve.JOne (M * p)) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) τ (e x)) := by sorry
