-- Prove2me | Theorems.Thm_TypeDensity_factor_cells_measure_preserving
-- name    : TypeDensity.factor_cells_measure_preserving
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T16:43:25.296608+00:00
-- url     : https://prove2.me/theorems/1c466ab5-8cab-48d9-9300-f1a96b817d6e
-- title:
--   Multiplying monic lifts of pairwise coprime monic residue polynomials `g i` pushes the product of the normalized cell measures forward to the normalized cell measure of `∏ i, g i`.
-- statement:
--   Multiplying monic lifts of pairwise coprime monic residue polynomials `g i` pushes the product of the normalized cell measures forward to the normalized cell measure of `∏ i, g i`.
-- source:
--   TypeDensity/Unramified/HomogeneousCells.lean#L96-L167

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_finite_coordinate_adic_congruence
import Theorems.Thm_TypeDensity_coefficient_uniformizer_cylinder_mass
import Theorems.Thm_TypeDensity_factor_product_continuous
import Theorems.Thm_TypeDensity_factor_product_bijection
import Theorems.Thm_TypeDensity_measurePreserving_cellMeasure_of_balls
import Theorems.Thm_TypeDensity_factor_product_congruence_iff
import Theorems.Thm_TypeDensity_residue_cell_cylinder
import Theorems.Thm_TypeDensity_residue_cell_mass
import Theorems.Thm_TypeDensity_factor_cell_product_measure
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

theorem TypeDensity.factor_cells_measure_preserving (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (ι : Type) [Fintype ι]
    (g : ι → Polynomial (IsLocalRing.ResidueField O)) (hg : ∀ i, (g i).Monic)
    (hc : ∀ i j, i ≠ j → IsCoprime (g i) (g j))
    [hσ : ∀ i, MeasureTheory.SigmaFinite
      (cellMeasure O (g i).natDegree (residueCell O (g i).natDegree (g i)))] :
    MeasureTheory.MeasurePreserving (factorProduct (fun i => (g i).natDegree))
      (MeasureTheory.Measure.pi
        (fun i => cellMeasure O (g i).natDegree (residueCell O (g i).natDegree (g i))))
      (cellMeasure O (∑ i, (g i).natDegree)
        (residueCell O (∑ i, (g i).natDegree) (∏ i, g i))) := by sorry
