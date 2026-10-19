-- Prove2me | Theorems.Thm_TypeDensity_overlap_level_generator_regular
-- name    : TypeDensity.overlap_level_generator_regular
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:17.190023+00:00
-- url     : https://prove2.me/theorems/f472f613-9400-4e59-9a00-112429b37812
-- title:
--   The images in the overlap of the generators `F j` of the level kernels of the opposite chart are nonzerodivisors modulo the powers of the exceptional divisor.
-- statement:
--   The images in the overlap of the generators `F j` of the level kernels of the opposite chart are nonzerodivisors modulo the powers of the exceptional divisor.
-- source:
--   TypeDensity/Blowup/NilpotentGluing.lean#L840-L867

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
import Theorems.Thm_TypeDensity_blowup_exceptional_parameter_regular
import Theorems.Thm_TypeDensity_regular_element_on_all_principal_power_quotients
import Theorems.Thm_TypeDensity_level_generator_ne_zero
import Theorems.Thm_TypeDensity_nonzerodivisor_survives_localization
import Theorems.Thm_TypeDensity_overlap_exceptional_quotient_domain
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

theorem TypeDensity.overlap_level_generator_regular (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] (hreg : RegularParameterPair R t x)
    (_hregSwap : RegularParameterPair R x t) (beta : BlowupRestriction R t x) (ι : Type) [Finite ι]
    (P : ι → Ideal (BlowupChart R x t)) [∀ i, (P i).IsMaximal] (hPe : ∀ i, chartBase R x t x ∈ P i)
    (g : ∀ i, CompletedLocalAt (BlowupChart R x t) (P i)) (L : ι → ℕ)
    (hfin : ∀ i, ((IsLocalRing.maximalIdeal (Localization.AtPrime (P i))).map
      (localCompletionMap (Localization.AtPrime (P i)))) ^ (L i) ≤ finiteLocalCurveIdeal
      (BlowupChart R x t) (P i) (chartBase R x t x) (g i) 1) (F : ℕ → BlowupChart R x t)
    (hF : ∀ j : ℕ, finiteSupportLevelKernel (BlowupChart R x t) ι P
      (fun i ↦ finiteLocalCurveIdeal (BlowupChart R x t) (P i) (chartBase R x t x) (g i) j)
      (chartBase R x t x) j = Ideal.span {Ideal.Quotient.mk ((Ideal.span {chartBase R x t x})^j)
      (F j)}) (j : ℕ) :
    Function.Injective (fun c : BlowupOverlap R t x ⧸ (Ideal.span {overlapException R t x})^j ↦
      Ideal.Quotient.mk ((Ideal.span {overlapException R t x})^j) (beta.right (F j)) * c) := by sorry
