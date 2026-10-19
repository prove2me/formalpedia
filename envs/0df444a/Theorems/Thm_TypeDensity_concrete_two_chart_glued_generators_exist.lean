-- Prove2me | Theorems.Thm_TypeDensity_concrete_two_chart_glued_generators_exist
-- name    : TypeDensity.concrete_two_chart_glued_generators_exist
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:39:02.988545+00:00
-- url     : https://prove2.me/theorems/753bc34f-4e96-4baf-a2f2-ae00d4f857ad
-- title:
--   A two-chart curve datum on a concrete surface `ConcreteSurface O pi u a b` comes from a global function `f` whose glued level generators cut out the left and right level kernels.
-- statement:
--   A two-chart curve datum on a concrete surface `ConcreteSurface O pi u a b` comes from a global function `f` whose glued level generators cut out the left and right level kernels.
-- source:
--   TypeDensity/Blowup/FixedTangentCellBijection.lean#L321-L352

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Formula_FiniteFieldCounts
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Definitions.Def_TypeDensity_Surfaces_TruncatedSeries
import Definitions.Def_TypeDensity_Surfaces_ConcreteAtlas
import Definitions.Def_TypeDensity_Blowup_DivisorPoints
import Definitions.Def_TypeDensity_Blowup_TwoChartCurveData
import Definitions.Def_TypeDensity_Recursion_Members
import Definitions.Def_TypeDensity_Measure_MemberCharts
import Definitions.Def_TypeDensity_Recursion_Termination
import Theorems.Thm_TypeDensity_two_chart_global_function_exists
import Theorems.Thm_TypeDensity_concrete_surface_isAdicComplete_parameterIdeal
import Theorems.Thm_TypeDensity_concrete_surface_parameterIdeal_isMaximal
import Theorems.Thm_TypeDensity_concrete_surface_isLocalRing
import Theorems.Thm_TypeDensity_blowupChart_concrete_isNoetherianRing
import Theorems.Thm_TypeDensity_concrete_surface_regular_pair_tx
import Theorems.Thm_TypeDensity_concrete_surface_regular_pair_xt
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

theorem TypeDensity.concrete_two_chart_glued_generators_exist (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) (beta : BlowupRestriction (ConcreteSurface O pi u a b)
        (surfaceT O pi u a b) (surfaceX O pi u a b))
    (D : TwoChartCurveData (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)
        beta) :
    ∃ f : ConcreteSurface O pi u a b, ∃ G : GluedGenerators (ConcreteSurface O pi u a b)
        (surfaceT O pi u a b) (surfaceX O pi u a b) beta (curveDataDegree D),
      (∀ j : ℕ, surfaceToCechInput (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
          (surfaceX O pi u a b) j f =
        (cechInputLattice (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)
            j).mkQ (gluedFunctionPair (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
                (surfaceX O pi u a b) G j)) ∧
      ∀ j : ℕ, Ideal.span {Ideal.Quotient.mk ((chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))^j) (G.left j)} = leftLevelKernel D j ∧
        Ideal.span {Ideal.Quotient.mk ((chartExceptional (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))^j) (G.right j)} = rightLevelKernel D j := by sorry
