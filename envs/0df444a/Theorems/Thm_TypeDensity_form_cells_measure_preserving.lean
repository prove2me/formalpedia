-- Prove2me | Theorems.Thm_TypeDensity_form_cells_measure_preserving
-- name    : TypeDensity.form_cells_measure_preserving
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T16:43:19.049139+00:00
-- url     : https://prove2.me/theorems/99a35fab-0d5f-41e5-8bfe-ad13e06c4238
-- title:
--   The homogeneous analogue of `factor_cells_measure_preserving`: the reduced form product map pushes the product of the normalized reduced form cell measures forward to the normalized reduced
-- statement:
--   The homogeneous analogue of `factor_cells_measure_preserving`: the reduced form product map pushes the product of the normalized reduced form cell measures forward to the normalized reduced form cell measure of the product form.
-- source:
--   TypeDensity/Unramified/HomogeneousCells.lean#L379-L426

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_form_product_maps_to_and_preserves
import Theorems.Thm_TypeDensity_normalized_form_cell_cylinder_mass
import Theorems.Thm_TypeDensity_form_cell_product_measure
import Theorems.Thm_TypeDensity_measurePreserving_cellMeasure_of_balls
import Theorems.Thm_TypeDensity_form_product_measurable
import Theorems.Thm_TypeDensity_form_product_congruence_reflects
import Theorems.Thm_TypeDensity_form_product_bijection
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

theorem TypeDensity.form_cells_measure_preserving (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (ι : Type) [Fintype ι] (d : ι → ℕ)
    (ν : ∀ i, Fin (d i + 1)) (g : ∀ i, Fin (d i + 1) → IsLocalRing.ResidueField O)
    (hgν : ∀ i, g i (ν i) = 1) (hc : FormsCoprime d g) (μ : Fin ((∑ i, d i) + 1))
    (hμ : formProd d g μ = 1)
    [hσ : ∀ i, MeasureTheory.SigmaFinite
      (cellMeasure O (d i) (reducedFormCell O (d i) (ν i) (g i)))] :
    MeasureTheory.MeasurePreserving (reducedFormProduct O d ν g μ)
      (MeasureTheory.Measure.pi
        (fun i => cellMeasure O (d i) (reducedFormCell O (d i) (ν i) (g i))))
      (cellMeasure O (∑ i, d i) (reducedFormCell O (∑ i, d i) μ (formProd d g))) := by sorry
