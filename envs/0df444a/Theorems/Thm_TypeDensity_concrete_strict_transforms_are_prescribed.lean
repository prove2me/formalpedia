-- Prove2me | Theorems.Thm_TypeDensity_concrete_strict_transforms_are_prescribed
-- name    : TypeDensity.concrete_strict_transforms_are_prescribed
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:45:19.565116+00:00
-- url     : https://prove2.me/theorems/075f69ad-96dc-4ad3-aa54-5877decbdf49
-- title:
--   The strict transforms of a curve `(f)` at the points of two-chart curve data are the prescribed local equations.
-- statement:
--   The strict transforms of a curve `(f)` at the points of two-chart curve data are the prescribed local equations.
-- source:
--   TypeDensity/Surfaces/ConcreteStrictTransforms.lean#L428-L478

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
import Definitions.Def_TypeDensity_Blowup_TwoChartCurveData
import Definitions.Def_TypeDensity_Surfaces_ConcreteAtlas
import Theorems.Thm_TypeDensity_strict_transform_left_point_equation
import Theorems.Thm_TypeDensity_principal_ideal_image
import Theorems.Thm_TypeDensity_global_function_strict_transform_at_right_point
import Theorems.Thm_TypeDensity_chartBase_apply_eq_algebraMap
import Theorems.Thm_TypeDensity_span_pow_mul_colon_eq
import Theorems.Thm_TypeDensity_two_chart_datum_concrete_instances
import Theorems.Thm_TypeDensity_two_chart_datum_concrete_transverse
import Theorems.Thm_TypeDensity_concrete_surface_parameterIdeal_isMaximal
import Theorems.Thm_TypeDensity_blowupChart_concrete_isNoetherianRing
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
set_option autoImplicit false

open TypeDensity
open scoped ENNReal

theorem TypeDensity.concrete_strict_transforms_are_prescribed (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a)
    (beta : BlowupRestriction (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b))
    (D : TwoChartCurveData (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b) beta) (f : ConcreteSurface O pi u a b)
    (G : GluedGenerators (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b) beta (curveDataDegree D))
    (hf : ∀ j : ℕ,
      surfaceToCechInput (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b) j f =
      (cechInputLattice (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b) j).mkQ
      (gluedFunctionPair (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b) G j))
    (hG : ∀ j : ℕ,
      Ideal.span
      {Ideal.Quotient.mk
      ((chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b))^j) (G.left j)} = leftLevelKernel D j ∧ Ideal.span
      {Ideal.Quotient.mk
      ((chartExceptional (ConcreteSurface O pi u a b) (surfaceX O pi u a b)
      (surfaceT O pi u a b))^j) (G.right j)} = rightLevelKernel D j) :
    (∀ s : D.ι ⊕ D.ι0,
        strictTransformAt (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)
        (leftPoint D s) (curveDataDegree D) (Ideal.span {f}) = Ideal.span {leftData D s}) ∧
      ∀ s : D.ι ⊕ D.ιinf,
      strictTransformAt (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)
      (rightPoint D s) (curveDataDegree D) (Ideal.span {f}) = Ideal.span {rightData D s} := by sorry
