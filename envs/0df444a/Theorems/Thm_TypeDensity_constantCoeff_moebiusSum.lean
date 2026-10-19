-- Prove2me | Theorems.Thm_TypeDensity_constantCoeff_moebiusSum
-- name    : TypeDensity.constantCoeff_moebiusSum
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:53.089006+00:00
-- url     : https://prove2.me/theorems/002a29f0-2d48-441e-827e-dd58659172f2
-- title:
--   `moebiusSum f` has constant term `0`.
-- statement:
--   `moebiusSum f` has constant term `0`.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L379-L381

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
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

theorem TypeDensity.constantCoeff_moebiusSum (f : Ser) : PowerSeries.constantCoeff (moebiusSum f) = 0 := by sorry
