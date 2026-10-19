-- Prove2me | Theorems.Thm_TypeDensity_dvr_extension_maximalIdeal_map_eq_pow
-- name    : TypeDensity.dvr_extension_maximalIdeal_map_eq_pow
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:04.900385+00:00
-- url     : https://prove2.me/theorems/af48aae7-826d-497b-b578-924ff610675f
-- title:
--   For an integral injective extension of DVRs `O → B`, `m_O B = m_B^e` with `e` the ramification index.
-- statement:
--   For an integral injective extension of DVRs `O → B`, `m_O B = m_B^e` with `e` the ramification index.
-- source:
--   TypeDensity/Unramified/Extension.lean#L453-L481

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
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
set_option autoImplicit false

open TypeDensity
open Polynomial IsLocalRing MeasureTheory

theorem TypeDensity.dvr_extension_maximalIdeal_map_eq_pow (O B : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra O B]
    [Algebra.IsIntegral O B] (hinj : Function.Injective (algebraMap O B)) :
    (IsLocalRing.maximalIdeal O).map (algebraMap O B) =
      (IsLocalRing.maximalIdeal B)^((IsLocalRing.maximalIdeal B).ramificationIdx O) := by sorry
