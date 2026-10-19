-- Prove2me | Theorems.Thm_TypeDensity_normalized_form_cell_cylinder_mass
-- name    : TypeDensity.normalized_form_cell_cylinder_mass
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:27.071818+00:00
-- url     : https://prove2.me/theorems/0fad19f2-d71a-4d08-ad68-b2843dca13c9
-- title:
--   The normalized form cell of `g` (residues prescribed, coordinate `ν` normalized to `1`) is a nonempty measurable residue class of mass `q^{-d}`;
-- statement:
--   The normalized form cell of `g` (residues prescribed, coordinate `ν` normalized to `1`) is a nonempty measurable residue class of mass `q^{-d}`; its normalized cell measure is a probability measure giving each congruence ball mod `m^L` mass `q^{-d(L-1)}`.
-- source:
--   TypeDensity/Unramified/FactorCells.lean#L209-L284

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Theorems.Thm_TypeDensity_finite_coordinate_adic_congruence
import Theorems.Thm_TypeDensity_finite_coordinate_borel_cylinders
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
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
set_option autoImplicit false

open TypeDensity
open scoped ENNReal

theorem TypeDensity.normalized_form_cell_cylinder_mass (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (d : ℕ) (ν : Fin (d + 1))
    (g : Fin (d + 1) → IsLocalRing.ResidueField O) (hgν : g ν = 1) :
    (∀ b : Fin d → O, b ∈ reducedFormCell O d ν g ↔
        ∀ j, IsLocalRing.residue O (b j) = g (ν.succAbove j)) ∧
      (∀ b ∈ reducedFormCell O d ν g,
        reducedFormCell O d ν g = {b' | ∀ j, b' j - b j ∈ (IsLocalRing.maximalIdeal O)}) ∧
      (reducedFormCell O d ν g).Nonempty ∧ MeasurableSet (reducedFormCell O d ν g) ∧
      coefficientMeasure O d (reducedFormCell O d ν g) =
        (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ^ d ∧
      MeasureTheory.IsProbabilityMeasure (cellMeasure O d (reducedFormCell O d ν g)) ∧
      ∀ (L : ℕ) (b : Fin d → O), 1 ≤ L → b ∈ reducedFormCell O d ν g →
        cellMeasure O d (reducedFormCell O d ν g)
            {b' | ∀ j, b' j - b j ∈ (IsLocalRing.maximalIdeal O) ^ L} =
          (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ^ (d * (L - 1)) := by sorry
