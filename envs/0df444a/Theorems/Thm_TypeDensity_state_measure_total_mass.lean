-- Prove2me | Theorems.Thm_TypeDensity_state_measure_total_mass
-- name    : TypeDensity.state_measure_total_mass
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:24.764314+00:00
-- url     : https://prove2.me/theorems/14245c29-95de-43b5-801b-4574e5713bfc
-- title:
--   An atlas whose chart maps are measurable has total state mass `#charts · q^(-n)`.
-- statement:
--   An atlas whose chart maps are measurable has total state mass `#charts · q^(-n)`.
-- source:
--   TypeDensity/Measure/PrimitiveLocus.lean#L89-L105

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Theorems.Thm_TypeDensity_chart_measure_total_mass
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

theorem TypeDensity.state_measure_total_mass (O R : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) [CommRing R] [Algebra O R]
    [MeasurableSpace (Ideal R)] (pi : O) (n : ℕ) (X : Set (Ideal R))
    (A : IdealAtlas O R pi n X)
    (hA : ∀ i, Measurable (coordinateIdeal pi (A.chart i).f (A.chart i).b)) :
    stateMeasure O R pi n (Nat.card (IsLocalRing.ResidueField O)) A Set.univ =
      (Fintype.card A.ι : ℝ≥0∞) * (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹^n := by sorry
