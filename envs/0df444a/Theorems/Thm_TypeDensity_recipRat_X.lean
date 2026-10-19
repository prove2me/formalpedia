-- Prove2me | Theorems.Thm_TypeDensity_recipRat_X
-- name    : TypeDensity.recipRat_X
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:52.394428+00:00
-- url     : https://prove2.me/theorems/41f92bc4-c75e-4c09-8135-7b8da07db742
-- title:
--   `recipRat q = q⁻¹`.
-- statement:
--   `recipRat q = q⁻¹`.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L295-L297

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

theorem TypeDensity.recipRat_X : recipRat RatFunc.X = RatFunc.X⁻¹ := by sorry
