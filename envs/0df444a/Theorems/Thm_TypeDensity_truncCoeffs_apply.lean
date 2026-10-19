-- Prove2me | Theorems.Thm_TypeDensity_truncCoeffs_apply
-- name    : TypeDensity.truncCoeffs_apply
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:47.924199+00:00
-- url     : https://prove2.me/theorems/b241bb15-3e15-4e8c-a879-48be3830bd46
-- title:
--   Evaluation of `truncCoeffs`.
-- statement:
--   `truncCoeffs` evaluates to the coefficient of `F` at the exponent corresponding to `s`.
-- source:
--   TypeDensity/Surfaces/TruncatedSeries.lean#L220-L223

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Surfaces_TruncatedSeries
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
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.truncCoeffs_apply (k : Type) [Field k] (a b L : ℕ) (F : TwoSeries k)
    (s : truncIndex a b L) :
    truncCoeffs k a b L F s = MvPowerSeries.coeff (truncExponent s.1) F := by sorry
