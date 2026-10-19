-- Prove2me | Theorems.Thm_TypeDensity_repeated_root_one_chart_atlas
-- name    : TypeDensity.repeated_root_one_chart_atlas
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:31:33.658985+00:00
-- url     : https://prove2.me/theorems/54d1dac3-e7d4-4ae4-b6e9-f7e554776dcc
-- title:
--   The state `single 1 r` on the concrete surface `(1, 1, 0)` admits a one-chart ideal atlas, with chart `x^r` and basis `(x^i)`, whose state measure is `q⁻ʳ` times the pushforward of the coefficient mea
-- statement:
--   The state `single 1 r` on the concrete surface `(1, 1, 0)` admits a one-chart ideal atlas, with chart `x^r` and basis `(x^i)`, whose state measure is `q⁻ʳ` times the pushforward of the coefficient measure under the coordinate ideal map.
-- source:
--   TypeDensity/Recursion/OrderDefect.lean#L786-L866

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
import Theorems.Thm_TypeDensity_special_fiber_single_contact_regular
import Theorems.Thm_TypeDensity_division_linear_equivalence
import Theorems.Thm_TypeDensity_single_residue_ideal_count
import Theorems.Thm_TypeDensity_series_quotient_equiv_adjoinRoot
import Theorems.Thm_TypeDensity_concrete_surface_residue_regular_of_special_fiber
import Theorems.Thm_TypeDensity_concrete_surface_special_fiber_equiv_parameters
import Theorems.Thm_TypeDensity_concrete_single_state_eq_union_cells
import Theorems.Thm_TypeDensity_concrete_surface_special_fiber_equiv
import Theorems.Thm_TypeDensity_axisQuotientLength_eq_top
import Theorems.Thm_TypeDensity_axisQuotientLength_eq
import Theorems.Thm_TypeDensity_contact_fiberT_eq_axisQuotientLength
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
open scoped BigOperators ENNReal TensorProduct

theorem TypeDensity.repeated_root_one_chart_atlas (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] [T2Space O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (pi : O) (hpi : Irreducible pi)
    [IsDomain (ConcreteSurface O pi 1 1 0)] [IsRegularLocalRing (ConcreteSurface O pi 1 1 0)]
    (S : SurfaceData O (ConcreteSurface O pi 1 1 0)) (hSpi : S.pi = pi)
    (hSt : S.t = surfaceT O pi 1 1 0) (hSa : S.a = 1)
    (hSb : S.b = 0) (r : ℕ) (hr : 0 < r) :
    ∃ A : IdealAtlas O (ConcreteSurface O pi 1 1 0) S.pi (State.single 1 r).degree
      (surfaceStateSet O (ConcreteSurface O pi 1 1 0) S (State.single 1 r)),
    ∃ i₀ : A.ι, (∀ i, i = i₀) ∧
    (A.chart i₀).f = (surfaceX O pi 1 1 0) ^ (State.single 1 r).degree ∧
    (A.chart i₀).b = (fun i : Fin (State.single 1 r).degree ↦ (surfaceX O pi 1 1 0) ^ i.val) ∧
    (letI : MeasurableSpace (Ideal (ConcreteSurface O pi 1 1 0)) :=
      idealChartSigma O (ConcreteSurface O pi 1 1 0) S.pi
    stateMeasure O (ConcreteSurface O pi 1 1 0) S.pi (State.single 1 r).degree
      (Nat.card (IsLocalRing.ResidueField O)) A =
    ((Nat.card (IsLocalRing.ResidueField O) : ℝ≥0∞)⁻¹ ^ (State.single 1 r).degree) •
      (coefficientMeasure O (State.single 1 r).degree).map
        (coordinateIdeal S.pi ((surfaceX O pi 1 1 0) ^ (State.single 1 r).degree)
          (fun i : Fin (State.single 1 r).degree ↦ (surfaceX O pi 1 1 0) ^ i.val))) := by sorry
