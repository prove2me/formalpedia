-- Prove2me | Theorems.Thm_TypeDensity_form_cell_product_measure
-- name    : TypeDensity.form_cell_product_measure
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:26.23089+00:00
-- url     : https://prove2.me/theorems/4fe8018b-86e9-48b4-9dca-a49cf4a80e72
-- title:
--   The product of the normalized cell measures of a family of form cells is a probability measure concentrated on the product cell, giving each congruence box mod `m^L` mass `q^{-(Σ dᵢ)(L-1)}`.
-- statement:
--   The product of the normalized cell measures of a family of form cells is a probability measure concentrated on the product cell, giving each congruence box mod `m^L` mass `q^{-(Σ dᵢ)(L-1)}`.
-- source:
--   TypeDensity/Unramified/FactorCells.lean#L286-L333

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Theorems.Thm_TypeDensity_normalized_form_cell_cylinder_mass
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

theorem TypeDensity.form_cell_product_measure (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (ι : Type) [Fintype ι] (d : ι → ℕ)
    (ν : ∀ i, Fin (d i + 1)) (g : ∀ i, Fin (d i + 1) → IsLocalRing.ResidueField O)
    (hgν : ∀ i, g i (ν i) = 1)
    [hσ : ∀ i,
      MeasureTheory.SigmaFinite (cellMeasure O (d i) (reducedFormCell O (d i) (ν i) (g i)))] :
    MeasureTheory.IsProbabilityMeasure
        (MeasureTheory.Measure.pi
          (fun i ↦ cellMeasure O (d i) (reducedFormCell O (d i) (ν i) (g i)))) ∧
      (MeasureTheory.Measure.pi (fun i ↦ cellMeasure O (d i) (reducedFormCell O (d i) (ν i) (g i))))
        (Set.pi Set.univ (fun i ↦ reducedFormCell O (d i) (ν i) (g i)))ᶜ = 0 ∧
      ∀ (L : ℕ), 1 ≤ L → ∀ a' ∈ Set.pi Set.univ (fun i ↦ reducedFormCell O (d i) (ν i) (g i)),
        (MeasureTheory.Measure.pi
            (fun i ↦ cellMeasure O (d i) (reducedFormCell O (d i) (ν i) (g i))))
          (Set.pi Set.univ (fun i ↦
            {b : Fin (d i) → O | ∀ j, b j - a' i j ∈ (IsLocalRing.maximalIdeal O) ^ L})) =
          (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ^ ((∑ i, d i) * (L - 1)) := by sorry
