-- Prove2me | Theorems.Thm_TypeDensity_expSer_logSer
-- name    : TypeDensity.expSer_logSer
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:02:27.689763+00:00
-- url     : https://prove2.me/theorems/2bcdb145-cc36-41f0-9812-70b531d95690
-- title:
--   `exp ∘ log = id` on series with constant term `1`.
-- statement:
--   `exp ∘ log = id` on series with constant term `1`.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L145-L151

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_constantCoeff_expSer
import Theorems.Thm_TypeDensity_derivative_expSer
import Theorems.Thm_TypeDensity_constantCoeff_logSer
import Theorems.Thm_TypeDensity_mul_derivative_logSer
import Theorems.Thm_TypeDensity_eq_of_mul_derivative_eq_mul
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

theorem TypeDensity.expSer_logSer (g : Ser) (hg : PowerSeries.constantCoeff g = 1) : expSer (logSer g) = g := by sorry
