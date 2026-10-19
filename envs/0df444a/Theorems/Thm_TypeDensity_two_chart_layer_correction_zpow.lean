-- Prove2me | Theorems.Thm_TypeDensity_two_chart_layer_correction_zpow
-- name    : TypeDensity.two_chart_layer_correction_zpow
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:45:24.434927+00:00
-- url     : https://prove2.me/theorems/26aa97f6-89bc-490f-81f0-452c44d2e09a
-- title:
--   Twisted layer correction with an arbitrary integral twist `k ≥ -1 - j`: an element of the `j`-th power of the exceptional ideal of the overlap is, modulo the `(j + 1)`-st power, of the form `a - z^k β
-- statement:
--   Twisted layer correction with an arbitrary integral twist `k ≥ -1 - j`: an element of the `j`-th power of the exceptional ideal of the overlap is, modulo the `(j + 1)`-st power, of the form `a - z^k β(b)` with `a`, `b` in the `j`-th powers of the exceptional ideals of the charts (`z` the slope).
-- source:
--   TypeDensity/Blowup/CurveSections.lean#L264-L342

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
import Theorems.Thm_TypeDensity_blowup_chart_relation
import Theorems.Thm_TypeDensity_laurent_split_nonnegative_twist
import Theorems.Thm_TypeDensity_overlap_layer_laurent_coordinates
import Theorems.Thm_TypeDensity_invSelf_pow_eq_selfZPow
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

theorem TypeDensity.two_chart_layer_correction_zpow (R : Type) [CommRing R] (t x : R)
    (hreg : RegularParameterPair R t x) (beta : BlowupChart R x t →+* BlowupOverlap R t x)
    (hbase : ∀ r : R, beta (chartBase R x t r) =
      algebraMap (BlowupChart R t x) (BlowupOverlap R t x) (chartBase R t x r))
    (hslope : beta (chartSlope R x t) = IsLocalization.Away.invSelf (chartSlope R t x))
    (j : ℕ) (k : ℤ) (hk : -1 ≤ (j : ℤ) + k) (w : BlowupOverlap R t x)
    (hw : w ∈ (Ideal.span {algebraMap (BlowupChart R t x) (BlowupOverlap R t x)
      (chartBase R t x t)})^j) :
    ∃ a ∈ (chartExceptional R t x)^j, ∃ b ∈ (chartExceptional R x t)^j,
      w - (algebraMap (BlowupChart R t x) (BlowupOverlap R t x) a -
        selfZPow (chartSlope R t x) (BlowupOverlap R t x) k * beta b) ∈
      (Ideal.span {algebraMap (BlowupChart R t x) (BlowupOverlap R t x)
        (chartBase R t x t)})^(j+1) := by sorry
