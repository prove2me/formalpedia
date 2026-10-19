-- Prove2me | Theorems.Thm_TypeDensity_strict_transform_left_point_equation
-- name    : TypeDensity.strict_transform_left_point_equation
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:53:23.428465+00:00
-- url     : https://prove2.me/theorems/76effee4-14a7-4ab5-bce9-b8942207c79d
-- title:
--   At a point of the first chart, the pullback of the surface function `f` factors in the completed local ring as `tᵈ · (local equation) · unit`.
-- statement:
--   At a point of the first chart, the pullback of the surface function `f` factors in the completed local ring as `tᵈ · (local equation) · unit`.
-- source:
--   TypeDensity/Blowup/CurveSections.lean#L1052-L1081

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
import Theorems.Thm_TypeDensity_curve_ideal_lattice_eq_kernels
import Theorems.Thm_TypeDensity_glued_function_left_chart
import Theorems.Thm_TypeDensity_strict_transform_equation_of_kernels
import Theorems.Thm_TypeDensity_two_chart_left_data_transverse_finite
import Theorems.Thm_TypeDensity_two_chart_left_points_maximal
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

theorem TypeDensity.strict_transform_left_point_equation (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] [IsNoetherianRing (BlowupChart R t x)]
    [IsNoetherianRing (BlowupChart R x t)] (beta : BlowupRestriction R t x)
    (D : TwoChartCurveData R t x beta) (d : ℕ) (G : GluedGenerators R t x beta d)
    (hG : ∀ j : ℕ, Ideal.span {Ideal.Quotient.mk ((chartExceptional R t x)^j) (G.left j)} =
      leftLevelKernel D j ∧ Ideal.span {Ideal.Quotient.mk ((chartExceptional R x t)^j) (G.right j)}
      = rightLevelKernel D j)
    (f : R)
    (hf : ∀ j : ℕ, surfaceToCechInput R t x j f =
      (cechInputLattice R t x j).mkQ (gluedFunctionPair R t x G j))
    (s : D.ι ⊕ D.ι0) [IsNoetherianRing (CompletedLocalAt (BlowupChart R t x) (leftPoint D s))]
    (hereg : Function.Injective (fun a : CompletedLocalAt (BlowupChart R t x) (leftPoint D s) =>
      completedPointMap (BlowupChart R t x) (leftPoint D s) (chartBase R t x t) * a))
    (hgreg : Function.Injective (fun a : CompletedLocalAt (BlowupChart R t x) (leftPoint D s) ⧸
      Ideal.span {completedPointMap (BlowupChart R t x) (leftPoint D s) (chartBase R t x t)} =>
      Ideal.Quotient.mk
      (Ideal.span {completedPointMap (BlowupChart R t x) (leftPoint D s) (chartBase R t x t)})
      (leftData D s) * a)) :
    ∃ v : (CompletedLocalAt (BlowupChart R t x) (leftPoint D s))ˣ, completedPointMap
      (BlowupChart R t x) (leftPoint D s) (algebraMap R (BlowupChart R t x) f) =
      (completedPointMap (BlowupChart R t x) (leftPoint D s) (chartBase R t x t))^d * leftData D s *
      (v : CompletedLocalAt (BlowupChart R t x) (leftPoint D s)) := by sorry
