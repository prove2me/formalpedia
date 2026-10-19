-- Prove2me | Theorems.Thm_TypeDensity_mvPowerSeries_mem_span_C_var_iff
-- name    : TypeDensity.mvPowerSeries_mem_span_C_var_iff
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:49.582176+00:00
-- url     : https://prove2.me/theorems/1534a9a4-fe04-4d8a-b930-2075a460aa29
-- title:
--   A series lies in `(c, X s)` iff `c` divides every coefficient whose `s`-exponent is zero.
-- statement:
--   A series lies in `(c, X s)` iff `c` divides every coefficient whose `s`-exponent is zero.
-- source:
--   TypeDensity/Surfaces/Lengths.lean#L531-L561

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
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

theorem TypeDensity.mvPowerSeries_mem_span_C_var_iff (σ A : Type) [CommRing A] (c : A) (s : σ)
    (g : MvPowerSeries σ A) :
    g ∈ Ideal.span {(MvPowerSeries.C c : MvPowerSeries σ A), MvPowerSeries.X s} ↔
    ∀ m : σ →₀ ℕ, m s = 0 → c ∣ MvPowerSeries.coeff m g := by sorry
