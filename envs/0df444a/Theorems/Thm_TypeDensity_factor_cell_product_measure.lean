-- Prove2me | Theorems.Thm_TypeDensity_factor_cell_product_measure
-- name    : TypeDensity.factor_cell_product_measure
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:04.847419+00:00
-- url     : https://prove2.me/theorems/db6c10dc-a7ac-4100-86cb-32c15c30aebe
-- title:
--   The product of the normalized factor-cell measures is a probability measure concentrated on the product of the cells, giving mass `q^(-(∑ deg g i)(L-1))` to each congruence box modulo `m^L`.
-- statement:
--   The product of the normalized factor-cell measures is a probability measure concentrated on the product of the cells, giving mass `q^(-(∑ deg g i)(L-1))` to each congruence box modulo `m^L`.
-- source:
--   TypeDensity/Unramified/PolynomialTypes.lean#L880-L944

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_coefficient_cylinder_mass
import Theorems.Thm_TypeDensity_residue_cell_cylinder
import Theorems.Thm_TypeDensity_residue_cell_mass
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

theorem TypeDensity.factor_cell_product_measure (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (ι : Type) [Fintype ι]
    (g : ι → Polynomial (IsLocalRing.ResidueField O)) (hg : ∀ i, (g i).Monic)
    [hσ : ∀ i, MeasureTheory.SigmaFinite
      (cellMeasure O (g i).natDegree (residueCell O (g i).natDegree (g i)))] :
    MeasureTheory.IsProbabilityMeasure
      (MeasureTheory.Measure.pi
        (fun i => cellMeasure O (g i).natDegree (residueCell O (g i).natDegree (g i)))) ∧
      (MeasureTheory.Measure.pi
        (fun i => cellMeasure O (g i).natDegree (residueCell O (g i).natDegree (g i))))
      (Set.pi Set.univ (fun i => residueCell O (g i).natDegree (g i)))ᶜ = 0 ∧ ∀ (L : ℕ), 1 ≤ L →
      ∀ a' ∈ Set.pi Set.univ (fun i => residueCell O (g i).natDegree (g i)),
      (MeasureTheory.Measure.pi
        (fun i => cellMeasure O (g i).natDegree (residueCell O (g i).natDegree (g i))))
      (Set.pi Set.univ
        (fun i =>
          {b : Fin (g i).natDegree → O | ∀ j, b j - a' i j ∈ (IsLocalRing.maximalIdeal O) ^ L})) =
      (Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ^ ((∑ i, (g i).natDegree) * (L - 1)) := by sorry
