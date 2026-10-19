-- Prove2me | Theorems.Thm_TypeDensity_actual_negative_twist_kernel_zero
-- name    : TypeDensity.actual_negative_twist_kernel_zero
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:52.219704+00:00
-- url     : https://prove2.me/theorems/5cbb51b3-776a-4cba-8d24-dbb8bea6195b
-- title:
--   In negative twist (`n ≤ d`), the finite Čech differential of the two-chart cover, truncated at level `n`, is injective.
-- statement:
--   In negative twist (`n ≤ d`), the finite Čech differential of the two-chart cover, truncated at level `n`, is injective.
-- source:
--   TypeDensity/Blowup/NilpotentGluing.lean#L304-L330

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
import Theorems.Thm_TypeDensity_chart_layer_polynomial_coordinates
import Theorems.Thm_TypeDensity_overlap_layer_laurent_coordinates
import Theorems.Thm_TypeDensity_principalLayerMap_apply_eq_mk
import Theorems.Thm_TypeDensity_invSelf_pow_eq_selfZPow
import Theorems.Thm_TypeDensity_beta_right_chartBase
import Theorems.Thm_TypeDensity_mk_mem_principalLayer
import Theorems.Thm_TypeDensity_negative_laurent_twist_has_no_kernel
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

theorem TypeDensity.actual_negative_twist_kernel_zero (R : Type) [CommRing R] (t x : R)
    (hreg : RegularParameterPair R t x) (beta : BlowupRestriction R t x)
    (hregSwap : RegularParameterPair R x t) (d n : ℕ) (hn : n ≤ d)
    (h : cechInputLattice R t x n ≤ (cechOutputLattice R t x n).comap
      (fullCechDifferential R t x beta d)) :
    Function.Injective (finiteCechDifferential R t x beta d n h) := by sorry
