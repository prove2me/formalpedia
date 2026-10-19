-- Prove2me | Theorems.Thm_TypeDensity_field_invariant_algEquiv
-- name    : TypeDensity.field_invariant_algEquiv
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:08.900259+00:00
-- url     : https://prove2.me/theorems/1114c70a-4cb9-4de1-815f-56e3e65f6e4c
-- title:
--   The invariants `(e, f)` of the integral closure of `O` in a finite extension `L/K` (assumed finite over `O`) depend only on the `K`-isomorphism class of `L`.
-- statement:
--   The invariants `(e, f)` of the integral closure of `O` in a finite extension `L/K` (assumed finite over `O`) depend only on the `K`-isomorphism class of `L`.
-- source:
--   TypeDensity/Algebra/FactorInvariant.lean#L35-L54

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_algebraMap_injective_of_tower
import Theorems.Thm_TypeDensity_integral_closure_algEquiv
import Theorems.Thm_TypeDensity_dvr_algEquiv_ramification_inertia
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
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
set_option autoImplicit false

open TypeDensity
open Polynomial

theorem TypeDensity.field_invariant_algEquiv (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (L L' : Type) [Field L] [Field L']
    [Algebra (BaseField O) L] [Algebra O L] [IsScalarTower O (BaseField O) L]
    [FiniteDimensional (BaseField O) L] [Algebra (BaseField O) L'] [Algebra O L']
    [IsScalarTower O (BaseField O) L'] [FiniteDimensional (BaseField O) L']
    (e : L ≃ₐ[BaseField O] L') (hfin : Module.Finite O (integralClosure O L)) :
    fieldInvariant O L = fieldInvariant O L' := by sorry
