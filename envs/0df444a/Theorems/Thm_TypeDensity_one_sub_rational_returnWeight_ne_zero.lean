-- Prove2me | Theorems.Thm_TypeDensity_one_sub_rational_returnWeight_ne_zero
-- name    : TypeDensity.one_sub_rational_returnWeight_ne_zero
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:38.833023+00:00
-- url     : https://prove2.me/theorems/8b3da2e4-53cc-4c4a-b8cb-f536c1ff06af
-- title:
--   For `n ≥ 2`, the return weight is not `1`: `1 - returnWeight n ≠ 0`.
-- statement:
--   For `n ≥ 2`, the return weight is not `1`: `1 - returnWeight n ≠ 0`.
-- source:
--   TypeDensity/Reciprocity/Patterns.lean#L466-L485

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Definitions.Def_TypeDensity_Reciprocity_Patterns
import Theorems.Thm_TypeDensity_rational_returnWeight
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

theorem TypeDensity.one_sub_rational_returnWeight_ne_zero (n : ℕ) (hn : 2 ≤ n) :
    1 - (returnWeight n).rational ≠ 0 := by sorry
