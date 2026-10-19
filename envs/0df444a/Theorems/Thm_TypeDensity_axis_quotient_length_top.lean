-- Prove2me | Theorems.Thm_TypeDensity_axis_quotient_length_top
-- name    : TypeDensity.axis_quotient_length_top
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T12:53:26.131319+00:00
-- url     : https://prove2.me/theorems/e8aac4e1-87a3-4e44-a764-f2106424f23b
-- title:
--   The quotient of `k[[T,X]]` by one variable has infinite length.
-- statement:
--   The quotient of `k[[T,X]]` by one variable has infinite length.
-- source:
--   TypeDensity/Surfaces/Lengths.lean#L473-L504

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

theorem TypeDensity.axis_quotient_length_top (k : Type) [Field k] (s t : Fin 2) (hst : s ≠ t) :
    Module.length (TwoSeries k) (TwoSeries k ⧸ Ideal.span {(MvPowerSeries.X s : TwoSeries k)}) =
    ⊤ := by sorry
