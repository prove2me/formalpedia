-- Prove2me | Theorems.Thm_TypeDensity_monicPolyO_map_fraction
-- name    : TypeDensity.monicPolyO_map_fraction
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:24.842407+00:00
-- url     : https://prove2.me/theorems/d51cdd44-fdda-4778-bc7d-fcc325d8f977
-- title:
--   The integral monic polynomial maps to the fraction-field monic polynomial `monicPolynomial`.
-- statement:
--   The integral monic polynomial maps to the fraction-field monic polynomial `monicPolynomial`.
-- source:
--   TypeDensity/Unramified/Extension.lean#L80-L83

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

theorem TypeDensity.monicPolyO_map_fraction (O : Type) [CommRing O] [IsDomain O] {n : ℕ} (a : Fin n → O) :
    (monicPolyO a).map (algebraMap O (BaseField O)) = monicPolynomial O a := by sorry
