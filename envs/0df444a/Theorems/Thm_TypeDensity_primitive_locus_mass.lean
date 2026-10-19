-- Prove2me | Theorems.Thm_TypeDensity_primitive_locus_mass
-- name    : TypeDensity.primitive_locus_mass
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:44.647284+00:00
-- url     : https://prove2.me/theorems/f45a2e24-ee60-40e5-9a15-bda88b7b9e19
-- title:
--   The primitive vectors of `O^(n+1)` (some coordinate a unit) have coefficient measure `1 - q^(-(n+1))`.
-- statement:
--   The primitive vectors of `O^(n+1)` (some coordinate a unit) have coefficient measure `1 - q^(-(n+1))`.
-- source:
--   TypeDensity/Measure/PrimitiveLocus.lean#L44-L75

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Theorems.Thm_TypeDensity_coefficient_cylinder_mass
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

theorem TypeDensity.primitive_locus_mass (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ) :
    coefficientMeasure O (n+1) {a | primitive O a} =
      1-(Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹^(n+1) := by sorry
