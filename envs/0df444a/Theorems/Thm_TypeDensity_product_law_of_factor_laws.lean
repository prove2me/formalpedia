-- Prove2me | Theorems.Thm_TypeDensity_product_law_of_factor_laws
-- name    : TypeDensity.product_law_of_factor_laws
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T16:48:43.999095+00:00
-- url     : https://prove2.me/theorems/24e27910-9e0f-44b8-93eb-1797e3fe28b4
-- title:
--   **Product law.** If the coprime factor cells have laws `Dl j`, then the product cell has law `lawProd (List.ofFn Dl)`.
-- statement:
--   **Product law.** If the coprime factor cells have laws `Dl j`, then the product cell has law `lawProd (List.ofFn Dl)`.
-- source:
--   TypeDensity/Assembly/MonicCells.lean#L247-L291

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Formula_FiniteFieldCounts
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Formula_PatternCounts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Definitions.Def_TypeDensity_Surfaces_TruncatedSeries
import Definitions.Def_TypeDensity_Blowup_TwoChartCurveData
import Definitions.Def_TypeDensity_Surfaces_ConcreteAtlas
import Definitions.Def_TypeDensity_Recursion_Members
import Definitions.Def_TypeDensity_Measure_MemberCharts
import Definitions.Def_TypeDensity_Recursion_Termination
import Definitions.Def_TypeDensity_Recursion_OrderDefect
import Definitions.Def_TypeDensity_Assembly_NullBridges
import Definitions.Def_TypeDensity_Assembly_TypeEvents
import Definitions.Def_TypeDensity_Assembly_MonicCells
import Theorems.Thm_TypeDensity_preimage_inter_pi_eq_biUnion
import Theorems.Thm_TypeDensity_measurableSet_inter_of_bijOn
import Theorems.Thm_TypeDensity_measure_eq_sum_prod_of_preimage
import Theorems.Thm_TypeDensity_sum_prod_densityValue_eq_lawProd
import Theorems.Thm_TypeDensity_coordinate_cylinder_clopen
import Theorems.Thm_TypeDensity_monic_polynomial_degree
import Theorems.Thm_TypeDensity_coprime_family_type_iff
import Theorems.Thm_TypeDensity_cellMeasure_cell_inter
import Theorems.Thm_TypeDensity_polynomial_type_degree
import Theorems.Thm_TypeDensity_monicPolyO_map_fraction
import Theorems.Thm_TypeDensity_coprime_of_coprime_residue_dvr
import Theorems.Thm_TypeDensity_factor_product_continuous
import Theorems.Thm_TypeDensity_monic_poly_reconstruct
import Theorems.Thm_TypeDensity_factor_product_bijection
import Theorems.Thm_TypeDensity_factor_cells_measure_preserving
import Theorems.Thm_TypeDensity_polynomial_type_unique
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
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.Algebra.Group.NatPowAssoc
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.product_law_of_factor_laws (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (L : ℕ)
    (g : Fin L → Polynomial (IsLocalRing.ResidueField O)) (hg : ∀ j, (g j).Monic)
    (hc : ∀ i j, i ≠ j → IsCoprime (g i) (g j)) (Dl : Fin L → Law)
    (hnn : ∀ (j : Fin L) (τ : FactorType), 0 ≤ (lawCoeff (Dl j) τ).eval
      (Nat.card (IsLocalRing.ResidueField O)))
    (hlaw : ∀ (j : Fin L) (τ : FactorType), MeasurableSet
      (residueCell O (g j).natDegree (g j) ∩ typeEvent O (g j).natDegree τ) ∧ cellMeasure O
      (g j).natDegree (residueCell O (g j).natDegree (g j)) (typeEvent O (g j).natDegree τ) =
      densityValue (lawCoeff (Dl j) τ) (Nat.card (IsLocalRing.ResidueField O))) (σ : FactorType) :
    MeasurableSet (residueCell O (∑ j, (g j).natDegree) (∏ j, g j) ∩ typeEvent O
      (∑ j, (g j).natDegree) σ) ∧ cellMeasure O (∑ j, (g j).natDegree)
      (residueCell O (∑ j, (g j).natDegree) (∏ j, g j)) (typeEvent O (∑ j, (g j).natDegree) σ) =
      densityValue (lawCoeff (lawProd (List.ofFn Dl)) σ)
      (Nat.card (IsLocalRing.ResidueField O)) := by sorry
