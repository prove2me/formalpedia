-- Prove2me | Theorems.Thm_TypeDensity_gaussPhi_sub
-- name    : TypeDensity.gaussPhi_sub
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:52.798576+00:00
-- url     : https://prove2.me/theorems/2daf617a-c374-4f5e-8af9-0294e9cf3d8e
-- title:
--   `Φ` is additive on differences.
-- statement:
--   `Φ` is additive on differences.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L700-L703

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

theorem TypeDensity.gaussPhi_sub (f g : Ser) : gaussPhi (f - g) = gaussPhi f - gaussPhi g := by sorry
