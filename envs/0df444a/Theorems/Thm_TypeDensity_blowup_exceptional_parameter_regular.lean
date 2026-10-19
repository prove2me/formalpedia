-- Prove2me | Theorems.Thm_TypeDensity_blowup_exceptional_parameter_regular
-- name    : TypeDensity.blowup_exceptional_parameter_regular
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:30.214624+00:00
-- url     : https://prove2.me/theorems/8f39fe03-3550-4db4-956b-ff099924707b
-- title:
--   If `(t, x)` is a regular sequence, then `t` is a nonzerodivisor on the `t`-chart.
-- statement:
--   If `(t, x)` is a regular sequence, then `t` is a nonzerodivisor on the `t`-chart.
-- source:
--   TypeDensity/Blowup/Charts.lean#L854-L891

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
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

theorem TypeDensity.blowup_exceptional_parameter_regular (R : Type) [CommRing R] (t x : R)
    (hreg : RegularParameterPair R t x) :
    Function.Injective (fun a : BlowupChart R t x => chartBase R t x t * a) := by sorry
