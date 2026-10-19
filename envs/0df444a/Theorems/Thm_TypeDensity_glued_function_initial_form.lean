-- Prove2me | Theorems.Thm_TypeDensity_glued_function_initial_form
-- name    : TypeDensity.glued_function_initial_form
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:45:06.317951+00:00
-- url     : https://prove2.me/theorems/4ad26cf1-18fd-476d-bf0a-6dd0fcef2463
-- title:
--   The glued function is a degree-`d` form `∑ cᵢ t^(d-i) xⁱ` whose dehomogenizations agree with the first glued generators modulo the exceptional ideals of the two charts.
-- statement:
--   The glued function is a degree-`d` form `∑ cᵢ t^(d-i) xⁱ` whose dehomogenizations agree with the first glued generators modulo the exceptional ideals of the two charts.
-- source:
--   TypeDensity/Blowup/H0Comparison.lean#L650-L694

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
import Theorems.Thm_TypeDensity_blowup_chart_relation
import Theorems.Thm_TypeDensity_blowup_exceptional_parameter_regular
import Theorems.Thm_TypeDensity_glued_function_left_chart
import Theorems.Thm_TypeDensity_glued_function_right_chart
import Theorems.Thm_TypeDensity_glued_function_order
import Theorems.Thm_TypeDensity_monomial_span_pow
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
open scoped BigOperators ENNReal

theorem TypeDensity.glued_function_initial_form (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (d : ℕ) (G : GluedGenerators R t x beta d)
    (hreg : RegularParameterPair R t x) (hregSwap : RegularParameterPair R x t) (f : R)
    (hf : ∀ j : ℕ, surfaceToCechInput R t x j f = (cechInputLattice R t x j).mkQ
    (gluedFunctionPair R t x G j)) :
    ∃ c : Fin (d+1) → R, f = ∑ i : Fin (d+1), c i * t^(d - i.val) * x^i.val ∧ G.left 1 - ∑ i : Fin
      (d+1), algebraMap R (BlowupChart R t x) (c i) * (chartSlope R t x)^i.val ∈ chartExceptional R
      t x ∧ G.right 1 - ∑ i : Fin (d+1), algebraMap R (BlowupChart R x t) (c i) *
      (chartSlope R x t)^(d - i.val) ∈ chartExceptional R x t := by sorry
