-- Prove2me | Theorems.Thm_TypeDensity_finite_measures_from_cylinders
-- name    : TypeDensity.finite_measures_from_cylinders
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:33.047995+00:00
-- url     : https://prove2.me/theorems/2e4529c8-ad87-477b-98d3-f4fb9682cd1c
-- title:
--   Two finite measures that agree on adic cylinders are equal, if the cylinders generate.
-- statement:
--   Two finite measures that agree on adic cylinders are equal, if the cylinders generate.
-- source:
--   TypeDensity/Measure/AdicTransport.lean#L220-L232

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Theorems.Thm_TypeDensity_adic_cylinders_intersection
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
set_option autoImplicit false

open TypeDensity
open scoped ENNReal

theorem TypeDensity.finite_measures_from_cylinders (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) [MeasurableSpace M] (mu nu : MeasureTheory.Measure M)
    [MeasureTheory.IsFiniteMeasure mu] (hgen : ‹MeasurableSpace M› = adicCylinderSpace I M)
    (heq : ∀ j x, mu {y | adicCongr I j y x} = nu {y | adicCongr I j y x}) :
    mu = nu := by sorry
