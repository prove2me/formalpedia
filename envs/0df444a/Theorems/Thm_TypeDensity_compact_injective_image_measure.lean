-- Prove2me | Theorems.Thm_TypeDensity_compact_injective_image_measure
-- name    : TypeDensity.compact_injective_image_measure
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:39.972476+00:00
-- url     : https://prove2.me/theorems/186a5659-67af-4117-89fa-8c3ae7edd317
-- title:
--   A continuous injective homomorphism from a compact group of image index `n` maps a measurable set of Haar mass `m` to a set of Haar mass `m / n`.
-- statement:
--   A continuous injective homomorphism from a compact group of image index `n` maps a measurable set of Haar mass `m` to a set of Haar mass `m / n`.
-- source:
--   TypeDensity/Measure/StateVolumes.lean#L190-L207

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
import Theorems.Thm_TypeDensity_finite_quotient_fiber_mass
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

theorem TypeDensity.compact_injective_image_measure (G H : Type) [AddCommGroup G] [AddCommGroup H]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [CompactSpace G] [MeasurableSpace G]
    [BorelSpace G] [TopologicalSpace H] [IsTopologicalAddGroup H] [T2Space H] [MeasurableSpace H]
    [BorelSpace H] (f : G →+ H) (hf : Continuous f) [Finite (H ⧸ f.range)]
    (hinj : Function.Injective f) (mu : MeasureTheory.Measure G)
    [MeasureTheory.IsProbabilityMeasure mu] [MeasureTheory.Measure.IsAddHaarMeasure mu]
    (nu : MeasureTheory.Measure H) [MeasureTheory.IsProbabilityMeasure nu]
    [MeasureTheory.Measure.IsAddLeftInvariant nu] (S : Set G) :
    nu (f '' S) = (f.range.index : ℝ≥0∞)⁻¹ * mu S := by sorry
