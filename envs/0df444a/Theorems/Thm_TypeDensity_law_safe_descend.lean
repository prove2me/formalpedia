-- Prove2me | Theorems.Thm_TypeDensity_law_safe_descend
-- name    : TypeDensity.law_safe_descend
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:02:11.041321+00:00
-- url     : https://prove2.me/theorems/6d51633c-ab2d-4ac6-91f9-52c0f2db6557
-- title:
--   Descents of safe laws are safe.
-- statement:
--   Descents of safe laws are safe.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L696-L709

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Theorems.Thm_TypeDensity_expression_pow_safe
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

theorem TypeDensity.law_safe_descend (δ : ℕ) (hδ : 0 < δ) (L : Law) (hL : LawSafe L) :
    LawSafe (lawDescend δ L) := by sorry
