-- Prove2me | Theorems.Thm_TypeDensity_logSer_expSer
-- name    : TypeDensity.logSer_expSer
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:02:22.784927+00:00
-- url     : https://prove2.me/theorems/0df36587-1fa8-4a93-9cea-23ccc2478ea4
-- title:
--   `log ∘ exp = id` on series with constant term `0`.
-- statement:
--   `log ∘ exp = id` on series with constant term `0`.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L153-L161

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_constantCoeff_expSer
import Theorems.Thm_TypeDensity_derivative_expSer
import Theorems.Thm_TypeDensity_constantCoeff_logSer
import Theorems.Thm_TypeDensity_mul_derivative_logSer
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Log
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.logSer_expSer (f : Ser) (hf : PowerSeries.constantCoeff f = 0) : logSer (expSer f) = f := by sorry
