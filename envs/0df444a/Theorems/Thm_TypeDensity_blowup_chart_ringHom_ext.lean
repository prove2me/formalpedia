-- Prove2me | Theorems.Thm_TypeDensity_blowup_chart_ringHom_ext
-- name    : TypeDensity.blowup_chart_ringHom_ext
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:12.53699+00:00
-- url     : https://prove2.me/theorems/57b38ac3-34b8-4f87-b9c3-5f913389c53b
-- title:
--   Ring maps out of a blow-up chart agree once they agree on `R` and on the slope.
-- statement:
--   Ring maps out of a blow-up chart agree once they agree on `R` and on the slope.
-- source:
--   TypeDensity/Blowup/Charts.lean#L833-L838

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

theorem TypeDensity.blowup_chart_ringHom_ext (R S : Type) [CommRing R] [CommRing S] (t x : R)
    (f g : BlowupChart R t x →+* S) (hbase : ∀ r : R, f (chartBase R t x r) = g (chartBase R t x r))
    (hslope : f (chartSlope R t x) = g (chartSlope R t x)) :
    f = g := by sorry
