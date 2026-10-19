-- Prove2me | Theorems.Thm_TypeDensity_integral_closure_own_adic_complete
-- name    : TypeDensity.integral_closure_own_adic_complete
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:49.479106+00:00
-- url     : https://prove2.me/theorems/e52ff72b-6906-454d-aaa5-51fd42b334b5
-- title:
--   The integral closure is complete for its own maximal ideal.
-- statement:
--   The integral closure is complete for its own maximal ideal.
-- source:
--   TypeDensity/Measure/PrimitiveLocus.lean#L246-L279

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Theorems.Thm_TypeDensity_adic_complete_iff_of_pow_le
import Theorems.Thm_TypeDensity_dvr_extension_maximalIdeal_map_eq_pow
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
open MeasureTheory
open scoped BigOperators ENNReal

theorem TypeDensity.integral_closure_own_adic_complete (O K L : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [Field L] [Algebra K L]
    [Algebra O L] [IsScalarTower O K L] [FiniteDimensional K L]
    [Module.Finite O (integralClosure O L)] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (hlocal : IsLocalRing (integralClosure O L)) :
    letI : IsLocalRing (integralClosure O L) := hlocal
    IsAdicComplete (IsLocalRing.maximalIdeal (integralClosure O L)) (integralClosure O L) := by sorry
