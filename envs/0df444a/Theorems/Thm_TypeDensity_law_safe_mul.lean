-- Prove2me | Theorems.Thm_TypeDensity_law_safe_mul
-- name    : TypeDensity.law_safe_mul
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:10.956819+00:00
-- url     : https://prove2.me/theorems/80f9df25-7cd6-4227-af08-10f81e213e99
-- title:
--   Products of safe laws are safe.
-- statement:
--   Products of safe laws are safe.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L711-L717

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
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
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.law_safe_mul (L M : Law) (hL : LawSafe L) (hM : LawSafe M) :
    LawSafe (lawMul L M) := by sorry
