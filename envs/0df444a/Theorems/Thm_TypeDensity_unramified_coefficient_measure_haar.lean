-- Prove2me | Theorems.Thm_TypeDensity_unramified_coefficient_measure_haar
-- name    : TypeDensity.unramified_coefficient_measure_haar
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:26.598744+00:00
-- url     : https://prove2.me/theorems/9ecfa5d2-a5a2-4341-9aae-f48898a10430
-- title:
--   The unramified coefficient measure on `O[X]/(Φ)` is an additive Haar probability measure, and the ball `x + (base ideal)^L` has mass `q^(-δL)`.
-- statement:
--   The unramified coefficient measure on `O[X]/(Φ)` is an additive Haar probability measure, and the ball `x + (base ideal)^L` has mass `q^(-δL)`.
-- source:
--   TypeDensity/Measure/PrimitiveLocus.lean#L147-L189

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Theorems.Thm_TypeDensity_power_coordinates_transport
import Theorems.Thm_TypeDensity_coefficient_cylinder_mass
import Theorems.Thm_TypeDensity_coefficient_measure_probability
import Theorems.Thm_TypeDensity_base_ideal_coordinates
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

theorem TypeDensity.unramified_coefficient_measure_haar (O : Type) [CommRing O] [IsDomain O]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O] (Φ : Polynomial O) (hm : Φ.Monic)
    [TopologicalSpace (AdjoinRoot Φ)]
    (hτ : ‹TopologicalSpace (AdjoinRoot Φ)› = unramifiedTopology O Φ hm)
    [MeasurableSpace (AdjoinRoot Φ)]
    (hmeas : ‹MeasurableSpace (AdjoinRoot Φ)› = unramifiedMeasurableSpace O Φ hm)
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (htop : IsAdic (IsLocalRing.maximalIdeal O)) :
    Measure.IsAddHaarMeasure (unramifiedCoefficientMeasure O Φ hm) ∧
      IsProbabilityMeasure (unramifiedCoefficientMeasure O Φ hm) ∧ ∀ (L : ℕ) (x : AdjoinRoot Φ),
      unramifiedCoefficientMeasure O Φ hm {y | y - x ∈ (baseIdeal O Φ) ^ L} =
      (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ^ (Φ.natDegree * L) := by sorry
