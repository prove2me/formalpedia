-- Prove2me | Theorems.Thm_TypeDensity_adjoinRoot_base_change
-- name    : TypeDensity.adjoinRoot_base_change
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:05.392281+00:00
-- url     : https://prove2.me/theorems/66bebbfd-4031-4ed0-9973-e0eff2a655ec
-- title:
--   Base change of `O[X]/(F)` to the fraction field `K` of `O` is `K[X]/(F)`, compatibly with `mk`.
-- statement:
--   Base change of `O[X]/(F)` to the fraction field `K` of `O` is `K[X]/(F)`, compatibly with `mk`.
-- source:
--   TypeDensity/Algebra/AlgebraType.lean#L221-L228

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Theorems.Thm_TypeDensity_adjoinRoot_tensor
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Henselian
set_option autoImplicit false

open TypeDensity
open scoped TensorProduct
open Polynomial IsLocalRing

theorem TypeDensity.adjoinRoot_base_change (O : Type) [CommRing O] [IsDomain O] (F : Polynomial O) :
    ∃ e : TensorProduct O (BaseField O) (AdjoinRoot F) ≃ₐ[BaseField O]
      AdjoinRoot (F.map (algebraMap O (BaseField O))), ∀ P : Polynomial O,
      e (TensorProduct.tmul O (1 : BaseField O) (AdjoinRoot.mk F P)) =
        AdjoinRoot.mk (F.map (algebraMap O (BaseField O))) (P.map (algebraMap O (BaseField O))) := by sorry
