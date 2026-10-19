-- Prove2me | Theorems.Thm_TypeDensity_lawWf_globalLaw
-- name    : TypeDensity.lawWf_globalLaw
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:00:40.281111+00:00
-- url     : https://prove2.me/theorems/86abc85e-c16e-4d43-87e1-267b161db3a4
-- title:
--   The global laws consist of well-formed expressions.
-- statement:
--   The global laws consist of well-formed expressions.
-- source:
--   TypeDensity/Reciprocity/Patterns.lean#L156-L158

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Definitions.Def_TypeDensity_Reciprocity_Patterns
import Theorems.Thm_TypeDensity_global_law_safe
import Theorems.Thm_TypeDensity_LawSafe_lawWf
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

theorem TypeDensity.lawWf_globalLaw (ε : Bool) (n : ℕ) : LawWf (globalLaw ε n) := by sorry
