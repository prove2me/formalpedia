-- Prove2me | Theorems.Thm_TypeDensity_axis_span_isPrime
-- name    : TypeDensity.axis_span_isPrime
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:13.891526+00:00
-- url     : https://prove2.me/theorems/f2c171a2-9e42-4383-adf4-fb1da7b6e112
-- title:
--   Each variable generates a prime ideal of `k[[T,X]]`.
-- statement:
--   Each variable generates a prime ideal of `k[[T,X]]`.
-- source:
--   TypeDensity/Surfaces/Lengths.lean#L586-L589

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Theorems.Thm_TypeDensity_mvPowerSeries_fin_two_span_C_var_isPrime
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

theorem TypeDensity.axis_span_isPrime (k : Type) [CommRing k] [IsDomain k] (s : Fin 2) :
    (Ideal.span {(MvPowerSeries.X s : TwoSeries k)}).IsPrime := by sorry
