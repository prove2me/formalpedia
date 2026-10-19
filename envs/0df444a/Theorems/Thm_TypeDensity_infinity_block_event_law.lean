-- Prove2me | Theorems.Thm_TypeDensity_infinity_block_event_law
-- name    : TypeDensity.infinity_block_event_law
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T17:02:25.873464+00:00
-- url     : https://prove2.me/theorems/98df78d4-a147-480c-a51c-0218daea52a9
-- title:
--   Assuming the root cell law, the reduced form cell at infinity has law `lawDescend 1 (stateLaw (single 1 r))` for its infinity block events.
-- statement:
--   Assuming the root cell law, the reduced form cell at infinity has law `lawDescend 1 (stateLaw (single 1 r))` for its infinity block events.
-- source:
--   TypeDensity/Assembly/MonicCells.lean#L885-L948

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
import Theorems.Thm_TypeDensity_reverse_polynomial_type_iff
import Theorems.Thm_TypeDensity_formPoly_coeff
import Theorems.Thm_TypeDensity_irreducible_cell_type_event
import Theorems.Thm_TypeDensity_cellMeasure_cell_inter
import Theorems.Thm_TypeDensity_coordinate_hyperplane_null
import Theorems.Thm_TypeDensity_monicPolyO_map_fraction
import Theorems.Thm_TypeDensity_monic_poly_reconstruct
import Theorems.Thm_TypeDensity_normalized_form_cell_cylinder_mass
import Theorems.Thm_TypeDensity_form_cell_monic_identification
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
open MeasureTheory
open MeasureTheory

theorem TypeDensity.infinity_block_event_law (hroot : RootCellLaw) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (htop : IsAdic (IsLocalRing.maximalIdeal O)) (r : ℕ) (hr : 0 < r) (σ : FactorType) :
    MeasurableSet (reducedFormCell O r (0 : Fin (r+1))
      (Pi.single (0 : Fin (r+1)) (1 : IsLocalRing.ResidueField O)) ∩ infinityBlockEvent O r σ) ∧
      cellMeasure O r (reducedFormCell O r (0 : Fin (r+1))
      (Pi.single (0 : Fin (r+1)) (1 : IsLocalRing.ResidueField O))) (infinityBlockEvent O r σ) =
      densityValue (lawCoeff (lawDescend 1 (stateLaw (State.single 1 r))) σ)
      (Nat.card (IsLocalRing.ResidueField O)) := by sorry
