-- Prove2me | Theorems.Thm_TypeDensity_t_chart_nonrational_point_child_data
-- name    : TypeDensity.t_chart_nonrational_point_child_data
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:15:44.696069+00:00
-- url     : https://prove2.me/theorems/db090abc-2e1d-42c5-8053-aecefc31fd47
-- title:
--   A closed point of degree `δ ≥ 2` on the exceptional line of the `t`-chart is cut out by an unramified lift `Φ` of degree `δ`, and its completed local ring is a concrete surface over `AdjoinRoot Φ` wit
-- statement:
--   A closed point of degree `δ ≥ 2` on the exceptional line of the `t`-chart is cut out by an unramified lift `Φ` of degree `δ`, and its completed local ring is a concrete surface over `AdjoinRoot Φ` with explicit `t`-parameter and `O`-structure.
-- source:
--   TypeDensity/Recursion/OrderDefect.lean#L973-L1044

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
import Theorems.Thm_TypeDensity_exceptional_line_equiv_chart_exceptional
import Theorems.Thm_TypeDensity_blowup_chart_exceptional_point_polynomial
import Theorems.Thm_TypeDensity_t_chart_nonrational_point_completion_equiv
import Theorems.Thm_TypeDensity_unramified_root_isUnit_of_two_le_natDegree
import Theorems.Thm_TypeDensity_concrete_chart_point_span_form
import Theorems.Thm_TypeDensity_chartSubst_apply_generators
import Theorems.Thm_TypeDensity_concrete_surface_quotient_parameters_equiv
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

theorem TypeDensity.t_chart_nonrational_point_child_data (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a)
    (P : Ideal (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b)))
    [P.IsMaximal] [P.IsPrime]
    (hP : (chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
        (surfaceT O pi u a b) ∈ P)
    (δ : ℕ)
    (hdeg : Module.length (ConcreteSurface O pi u a b)
        ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) ⧸
          P) = (δ : ℕ∞))
    (h2 : 2 ≤ δ) :
    ∃ Φ : Polynomial O, IsUnramifiedLift O Φ ∧ Φ.natDegree = δ ∧
    P = Ideal.span {(chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b)) (surfaceT O pi u a b),
        Polynomial.eval₂ ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b)).comp (algebraMap O (ConcreteSurface O pi u a b)))
        (chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) Φ} ∧
    ∃ (hθ : IsUnit (AdjoinRoot.root Φ))
        (Eq : CompletedLocalAt (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b)) P ≃+*
        ConcreteSurface (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi)
        (substUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ)
        (baseChangeUnit O (algebraMap O (AdjoinRoot Φ)) u) *
        shiftUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ) hθ ^ b) (a + b) 0),
    Eq ((completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b)) P) ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b)) (surfaceT O pi u a b))) =
        surfaceT (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi)
        (substUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ)
        (baseChangeUnit O (algebraMap O (AdjoinRoot Φ)) u) *
        shiftUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ) hθ ^ b) (a + b) 0 ∧
    ∀ c : O,
    Eq ((completedPointMap (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b)) P) ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b)) (algebraMap O (ConcreteSurface O pi u a b) c))) =
        algebraMap (AdjoinRoot Φ) (ConcreteSurface (AdjoinRoot Φ) (algebraMap O (AdjoinRoot Φ) pi)
        (substUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ)
        (baseChangeUnit O (algebraMap O (AdjoinRoot Φ)) u) *
        shiftUnit (AdjoinRoot Φ) (AdjoinRoot.root Φ) hθ ^ b) (a + b) 0)
        (algebraMap O (AdjoinRoot Φ) c) := by sorry
