-- Prove2me | Theorems.Thm_TypeDensity_residue_cell_mass
-- name    : TypeDensity.residue_cell_mass
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:05.577061+00:00
-- url     : https://prove2.me/theorems/9cbebfb7-219c-4361-aa67-703ce9ee1469
-- title:
--   A nonempty residue cell is measurable of mass `q^(-n)`, and its normalized cell measure is a probability measure.
-- statement:
--   A nonempty residue cell is measurable of mass `q^(-n)`, and its normalized cell measure is a probability measure.
-- source:
--   TypeDensity/Unramified/PolynomialTypes.lean#L837-L878

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_finite_coordinate_adic_congruence
import Theorems.Thm_TypeDensity_finite_coordinate_borel_cylinders
import Theorems.Thm_TypeDensity_coefficient_cylinder_mass
import Theorems.Thm_TypeDensity_residue_cell_cylinder
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
open scoped ENNReal

theorem TypeDensity.residue_cell_mass (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (n : ℕ)
    (G : Polynomial (IsLocalRing.ResidueField O)) (hG : G.Monic) (hGn : G.natDegree = n) :
    MeasurableSet (residueCell O n G) ∧ coefficientMeasure O n (residueCell O n G) =
      (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ^ n ∧ MeasureTheory.IsProbabilityMeasure
      (cellMeasure O n (residueCell O n G)) := by sorry
