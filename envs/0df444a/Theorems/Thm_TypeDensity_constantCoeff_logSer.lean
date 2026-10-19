-- Prove2me | Theorems.Thm_TypeDensity_constantCoeff_logSer
-- name    : TypeDensity.constantCoeff_logSer
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:51.663657+00:00
-- url     : https://prove2.me/theorems/2682d514-f917-42f1-a9e8-22adce69d115
-- title:
--   `log g` has constant term `0` when `g(0) = 1`.
-- statement:
--   `log g` has constant term `0` when `g(0) = 1`.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L445-L448

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

theorem TypeDensity.constantCoeff_logSer (g : Ser) (hg : PowerSeries.constantCoeff g = 1) :
    PowerSeries.constantCoeff (logSer g) = 0 := by sorry
