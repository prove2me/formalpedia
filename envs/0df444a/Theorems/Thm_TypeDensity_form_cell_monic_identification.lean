-- Prove2me | Theorems.Thm_TypeDensity_form_cell_monic_identification
-- name    : TypeDensity.form_cell_monic_identification
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:24.837299+00:00
-- url     : https://prove2.me/theorems/0d0638c7-fd43-4163-9c69-930fe4b6cbb3
-- title:
--   Reduced form cells normalized at the last coordinate are monic residue cells;
-- statement:
--   Reduced form cells normalized at the last coordinate are monic residue cells; coordinate reversal is a bijection, compatible with congruences and measure preserving, from the reduced form cell of `X ^ r` normalized at `0` onto the monic residue cell of `X ^ r`.
-- source:
--   TypeDensity/Unramified/HomogeneousCells.lean#L240-L303

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_finite_coordinate_adic_congruence
import Theorems.Thm_TypeDensity_finite_coordinate_borel_cylinders
import Theorems.Thm_TypeDensity_finite_measures_from_cylinders
import Theorems.Thm_TypeDensity_coefficient_cylinder_mass
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.form_cell_monic_identification (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (r : ℕ) :
    (∀ (d : ℕ) (g : Fin (d+1) → IsLocalRing.ResidueField O),
      reducedFormCell O d (Fin.last d) g = residueCell O d (formPoly g)) ∧
    Set.BijOn (fun b : Fin r → O => b ∘ Fin.rev) (reducedFormCell O r 0 (Pi.single 0 1))
      (residueCell O r (Polynomial.X ^ r)) ∧
    (∀ (L : ℕ) (b b' : Fin r → O), (∀ j, b j - b' j ∈ (IsLocalRing.maximalIdeal O) ^ L) ↔
      ∀ j, (b ∘ Fin.rev) j - (b' ∘ Fin.rev) j ∈ (IsLocalRing.maximalIdeal O) ^ L) ∧
    MeasureTheory.MeasurePreserving (fun b : Fin r → O => b ∘ Fin.rev)
      (cellMeasure O r (reducedFormCell O r 0 (Pi.single 0 1)))
      (cellMeasure O r (residueCell O r (Polynomial.X ^ r))) := by sorry
