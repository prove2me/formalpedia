-- Prove2me | Theorems.Thm_TypeDensity_special_fiber_single_contact_regular
-- name    : TypeDensity.special_fiber_single_contact_regular
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:12.995479+00:00
-- url     : https://prove2.me/theorems/03884ac6-f36b-42bb-baa5-9a4e34972f43
-- title:
--   On the single special fiber `k⟦t, x⟧ ⧸ (tᵃ)` with `a > 0`, a function of finite contact with the axis `t = 0` is a nonzerodivisor.
-- statement:
--   On the single special fiber `k⟦t, x⟧ ⧸ (tᵃ)` with `a > 0`, a function of finite contact with the axis `t = 0` is a nonzerodivisor.
-- source:
--   TypeDensity/Blowup/StrictNormalizer.lean#L652-L671

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Formula_FiniteFieldCounts
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Definitions.Def_TypeDensity_Surfaces_TruncatedSeries
import Theorems.Thm_TypeDensity_not_mem_axis_of_contact
import Theorems.Thm_TypeDensity_mem_axis_pow_of_mul_mem
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
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.Algebra.Group.NatPowAssoc
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.special_fiber_single_contact_regular (k : Type) [Field k] (a c : ℕ) (ha : 0 < a)
    (f : SpecialFiber k a 0) (hf : contact f (fiberT k a 0) = c) :
    Function.Injective (fun w : SpecialFiber k a 0 => f * w) := by sorry
