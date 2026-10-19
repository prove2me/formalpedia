-- Prove2me | Theorems.Thm_TypeDensity_integral_closure_invariants_degree
-- name    : TypeDensity.integral_closure_invariants_degree
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:04.079515+00:00
-- url     : https://prove2.me/theorems/eb6ea36e-8718-4e73-8756-c9a66174e91b
-- title:
--   Over a complete DVR with finite residue field, if the (finite) integral closure of `O` in `L` is local, its ramification index and inertia degree are positive with `e · f = [L : K]`.
-- statement:
--   Over a complete DVR with finite residue field, if the (finite) integral closure of `O` in `L` is local, its ramification index and inertia degree are positive with `e · f = [L : K]`.
-- source:
--   TypeDensity/Algebra/AlgebraType.lean#L474-L488

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Theorems.Thm_TypeDensity_finite_flat_local_ramification_degree
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

theorem TypeDensity.integral_closure_invariants_degree (O K L : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [Field L] [Algebra K L]
    [Algebra O L] [IsScalarTower O K L] [FiniteDimensional K L]
    [Module.Finite O (integralClosure O L)] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (hlocal : IsLocalRing (integralClosure O L)) :
    letI : IsLocalRing (integralClosure O L) := hlocal;
      0 < (IsLocalRing.maximalIdeal (integralClosure O L)).ramificationIdx O ∧
      0 < (IsLocalRing.maximalIdeal (integralClosure O L)).inertiaDeg O ∧
      (IsLocalRing.maximalIdeal (integralClosure O L)).ramificationIdx O *
        (IsLocalRing.maximalIdeal (integralClosure O L)).inertiaDeg O = Module.finrank K L := by sorry
