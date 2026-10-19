-- Prove2me | Theorems.Thm_TypeDensity_binomial_series_ode
-- name    : TypeDensity.binomial_series_ode
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:43.400551+00:00
-- url     : https://prove2.me/theorems/c9102337-e792-44c2-986c-dc3b88b5cb2f
-- title:
--   The binomial series `Σ C(c,n) xⁿ` solves `(1 + x) y' = c y`.
-- statement:
--   The binomial series `Σ C(c,n) xⁿ` solves `(1 + x) y' = c y`.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L395-L419

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Log
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.binomial_series_ode (c : RatFunc ℚ) :
    (1 + PowerSeries.X) * PowerSeries.derivative Coef (PowerSeries.mk fun n ↦
      ((n.factorial : ℚ)⁻¹) • ∏ j ∈ Finset.range n, (scalar c - (j : ℚ) • (1 : Coef))) =
    PowerSeries.C (scalar c) * PowerSeries.mk (fun n ↦
      ((n.factorial : ℚ)⁻¹) • ∏ j ∈ Finset.range n, (scalar c - (j : ℚ) • (1 : Coef))) := by sorry
