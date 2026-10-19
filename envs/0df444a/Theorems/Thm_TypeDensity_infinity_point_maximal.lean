-- Prove2me | Theorems.Thm_TypeDensity_infinity_point_maximal
-- name    : TypeDensity.infinity_point_maximal
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:52.76896+00:00
-- url     : https://prove2.me/theorems/ace469b9-3f21-498d-90fa-f46dba937382
-- title:
--   The point at infinity of the opposite chart is a maximal ideal containing `x` and the slope, with `R`-length one.
-- statement:
--   The point at infinity of the opposite chart is a maximal ideal containing `x` and the slope, with `R`-length one.
-- source:
--   TypeDensity/Blowup/ExceptionalLayers.lean#L618-L695

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
import Theorems.Thm_TypeDensity_blowup_chart_relation
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
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.infinity_point_maximal (O R : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing R] [IsDomain R] [Algebra O R] [IsRegularLocalRing R] (S : SurfaceData O R) :
    (infinityPoint R S.t S.x).IsMaximal ∧ chartBase R S.x S.t S.x ∈ infinityPoint R S.t S.x ∧
    chartSlope R S.x S.t ∈ infinityPoint R S.t S.x ∧ Module.length R
    (BlowupChart R S.x S.t ⧸ infinityPoint R S.t S.x) = 1 := by sorry
