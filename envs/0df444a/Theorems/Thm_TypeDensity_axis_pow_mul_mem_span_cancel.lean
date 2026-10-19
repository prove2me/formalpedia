-- Prove2me | Theorems.Thm_TypeDensity_axis_pow_mul_mem_span_cancel
-- name    : TypeDensity.axis_pow_mul_mem_span_cancel
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:31:51.643042+00:00
-- url     : https://prove2.me/theorems/a078e4e2-c78a-421c-ae91-b8d1291ea3e5
-- title:
--   If `F` is not divisible by the variable `X s`, then `X s ^ n * G ∈ (F)` implies `G ∈ (F)`.
-- statement:
--   If `F` is not divisible by the variable `X s`, then `X s ^ n * G ∈ (F)` implies `G ∈ (F)`.
-- source:
--   TypeDensity/Surfaces/Lengths.lean#L591-L613

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Theorems.Thm_TypeDensity_axis_span_isPrime
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.axis_pow_mul_mem_span_cancel (k : Type) [Field k] (s : Fin 2) (F : TwoSeries k)
    (hF : F ∉ Ideal.span {(MvPowerSeries.X s : TwoSeries k)}) (n : ℕ) (G : TwoSeries k)
    (hG : (MvPowerSeries.X s : TwoSeries k) ^ n * G ∈ Ideal.span {F}) :
    G ∈ Ideal.span {F} := by sorry
