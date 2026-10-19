-- Prove2me | Theorems.Thm_TypeDensity_recipRat_C
-- name    : TypeDensity.recipRat_C
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:55.879801+00:00
-- url     : https://prove2.me/theorems/7cdb3841-e03e-4dd3-895d-7c7dcae484d5
-- title:
--   `recipRat` fixes the constants.
-- statement:
--   `recipRat` fixes the constants.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L287-L289

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Theorems.Thm_TypeDensity_recipRat_algebraMap
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

theorem TypeDensity.recipRat_C (r : ℚ) : recipRat (RatFunc.C r) = RatFunc.C r := by sorry
