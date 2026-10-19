-- Prove2me | Theorems.Thm_TypeDensity_surface_threads_range
-- name    : TypeDensity.surface_threads_range
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:00:17.148164+00:00
-- url     : https://prove2.me/theorems/71f9da28-87d6-44a9-96bf-e1d9dc4b6be8
-- title:
--   For complete `R`, the image of `R` in Čech threads is the intersection of the kernels of the levelwise twist-`0` Čech differentials.
-- statement:
--   For complete `R`, the image of `R` in Čech threads is the intersection of the kernels of the levelwise twist-`0` Čech differentials.
-- source:
--   TypeDensity/Blowup/H0Comparison.lean#L884-L938

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
import Theorems.Thm_TypeDensity_surface_section_closed
import Theorems.Thm_TypeDensity_surface_to_cech_kernel
import Theorems.Thm_TypeDensity_surface_to_cech_range
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

theorem TypeDensity.surface_threads_range (R : Type) [CommRing R] (t x : R)
    [IsAdicComplete (Ideal.span {t,x}) R] (hreg : RegularParameterPair R t x)
    (hregSwap : RegularParameterPair R x t) (beta : BlowupRestriction R t x)
    (hpres : ∀ j : ℕ, cechInputLattice R t x j ≤ (cechOutputLattice R t x j).comap
    (fullCechDifferential R t x beta 0)) :
    LinearMap.range (surfaceThreads R t x) = ⨅ j : ℕ, LinearMap.ker
      ((finiteCechDifferential R t x beta 0 j (hpres j)).comp (cechInputThreadLinear R t x j)) := by sorry
