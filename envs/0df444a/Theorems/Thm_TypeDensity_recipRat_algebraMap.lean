-- Prove2me | Theorems.Thm_TypeDensity_recipRat_algebraMap
-- name    : TypeDensity.recipRat_algebraMap
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:12.973024+00:00
-- url     : https://prove2.me/theorems/e0b6de0c-143c-436a-bcce-f34e719c0032
-- title:
--   `recipRat` extends `recipPoly`.
-- statement:
--   `recipRat` extends `recipPoly`.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L282-L285

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

theorem TypeDensity.recipRat_algebraMap (g : Polynomial ℚ) :
    recipRat (algebraMap (Polynomial ℚ) (RatFunc ℚ) g) = recipPoly g := by sorry
