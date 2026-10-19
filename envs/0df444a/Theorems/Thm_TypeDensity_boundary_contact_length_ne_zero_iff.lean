-- Prove2me | Theorems.Thm_TypeDensity_boundary_contact_length_ne_zero_iff
-- name    : TypeDensity.boundary_contact_length_ne_zero_iff
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:41.310156+00:00
-- url     : https://prove2.me/theorems/8dedcb9a-359e-4edd-9582-ab050b0b1462
-- title:
--   On the chart at infinity, the curve `∑ cᵢ W^(d-i)` meets the boundary `W = 0` iff its constant coefficient `c_d` lies in the maximal ideal.
-- statement:
--   On the chart at infinity, the curve `∑ cᵢ W^(d-i)` meets the boundary `W = 0` iff its constant coefficient `c_d` lies in the maximal ideal.
-- source:
--   TypeDensity/Recursion/Members.lean#L488-L536

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
import Definitions.Def_TypeDensity_Blowup_TwoChartCurveData
import Definitions.Def_TypeDensity_Surfaces_ConcreteAtlas
import Definitions.Def_TypeDensity_Recursion_Members
import Theorems.Thm_TypeDensity_boundary_chart_quotient_equiv
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
open IsLocalRing MeasureTheory
open scoped BigOperators ENNReal

theorem TypeDensity.boundary_contact_length_ne_zero_iff (R : Type) [CommRing R] [IsLocalRing R] (t x : R)
    (hmax : maximalIdeal R = Ideal.span {t, x}) (d : ℕ) (c : Fin (d + 1) → R) :
    Module.length (BlowupChart R x t) (BlowupChart R x t ⧸ (Ideal.span
      {(∑ i : Fin (d+1), algebraMap R (BlowupChart R x t) (c i) * (chartSlope R x t)^(d - i.val))} ⊔
      Ideal.span {chartSlope R x t})) ≠ 0 ↔ c (Fin.last d) ∈ maximalIdeal R := by sorry
