-- Prove2me | Theorems.Thm_TypeDensity_boundary_chart_quotient_equiv
-- name    : TypeDensity.boundary_chart_quotient_equiv
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:41.113304+00:00
-- url     : https://prove2.me/theorems/b97c7ce3-f013-4a46-9f54-55ae5c162783
-- title:
--   The `x`-chart modulo its slope `W` is `R/(t)`, compatibly with the structure maps.
-- statement:
--   The `x`-chart modulo its slope `W` is `R/(t)`, compatibly with the structure maps.
-- source:
--   TypeDensity/Blowup/Charts.lean#L893-L941

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Theorems.Thm_TypeDensity_blowup_chart_relation
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

theorem TypeDensity.boundary_chart_quotient_equiv (R : Type) [CommRing R] (t x : R) :
    ∃ ρ : (BlowupChart R x t ⧸ Ideal.span {chartSlope R x t}) ≃+* (R ⧸ Ideal.span {t}),
        (∀ r : R, ρ (Ideal.Quotient.mk (Ideal.span {chartSlope R x t}) (chartBase R x t r)) =
        Ideal.Quotient.mk (Ideal.span {t}) r) ∧ ρ (Ideal.Quotient.mk (Ideal.span {chartSlope R x t})
        (chartSlope R x t)) = 0 := by sorry
