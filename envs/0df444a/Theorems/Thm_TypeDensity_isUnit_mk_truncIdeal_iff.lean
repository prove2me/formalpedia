-- Prove2me | Theorems.Thm_TypeDensity_isUnit_mk_truncIdeal_iff
-- name    : TypeDensity.isUnit_mk_truncIdeal_iff
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:45.126983+00:00
-- url     : https://prove2.me/theorems/180ab9e1-4d35-440d-9e08-58b1b69001c3
-- title:
--   For `0 < a` and `0 < L`, the class of `F` in `k⟦T, X⟧ ⧸ truncIdeal k a b L` is a unit iff the constant coefficient of `F` is nonzero.
-- statement:
--   For `0 < a` and `0 < L`, the class of `F` in `k⟦T, X⟧ ⧸ truncIdeal k a b L` is a unit iff the constant coefficient of `F` is nonzero.
-- source:
--   TypeDensity/Surfaces/TruncatedSeries.lean#L305-L318

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

theorem TypeDensity.isUnit_mk_truncIdeal_iff (k : Type) [Field k] (a b L : ℕ) (ha : 0 < a) (hL : 0 < L)
    (F : TwoSeries k) :
    IsUnit (Ideal.Quotient.mk (truncIdeal k a b L) F) ↔ MvPowerSeries.constantCoeff F ≠ 0 := by sorry
