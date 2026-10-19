-- Prove2me | Theorems.Thm_TypeDensity_patternSum_eq_of_le
-- name    : TypeDensity.patternSum_eq_of_le
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:17.80298+00:00
-- url     : https://prove2.me/theorems/06f265b4-7f7e-4443-a348-d92ba70d16d4
-- title:
--   The pattern sum of weight `w` is independent of the ambient dimension, as long as it is at least `w`.
-- statement:
--   The pattern sum of weight `w` is independent of the ambient dimension, as long as it is at least `w`.
-- source:
--   TypeDensity/Reciprocity/Patterns.lean#L145-L150

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Definitions.Def_TypeDensity_Reciprocity_Patterns
import Theorems.Thm_TypeDensity_pattern_entry_le_patternWeight
import Theorems.Thm_TypeDensity_pattern_entry_eq_zero_of_lt
import Theorems.Thm_TypeDensity_rational_divisorCount
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

theorem TypeDensity.patternSum_eq_of_le (ε : ℤ) (a N N' w : ℕ) (hN : w ≤ N) (hN' : w ≤ N') :
    patternSum ε a N w = patternSum ε a N' w := by sorry
