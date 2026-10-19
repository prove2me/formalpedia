-- Prove2me | Theorems.Thm_TypeDensity_plethSum_add
-- name    : TypeDensity.plethSum_add
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:49.228983+00:00
-- url     : https://prove2.me/theorems/4be46933-7eb4-4654-96cf-db4d03e2a7fc
-- title:
--   `plethSum` is additive.
-- statement:
--   `plethSum` is additive.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L371-L373

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

theorem TypeDensity.plethSum_add (f g : Ser) : plethSum (f + g) = plethSum f + plethSum g := by sorry
