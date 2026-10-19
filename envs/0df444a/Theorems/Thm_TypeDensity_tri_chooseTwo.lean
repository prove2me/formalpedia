-- Prove2me | Theorems.Thm_TypeDensity_tri_chooseTwo
-- name    : TypeDensity.tri_chooseTwo
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:53.315982+00:00
-- url     : https://prove2.me/theorems/12f9b15e-9e2e-48f7-b2b4-ba5b9b298bee
-- title:
--   `tri d = chooseTwo d + d`.
-- statement:
--   `tri d = chooseTwo d + d`.
-- source:
--   TypeDensity/Formula/StateCombinatorics.lean#L396-L405

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
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

theorem TypeDensity.tri_chooseTwo (d : ℕ) :
    tri d = chooseTwo d + d := by sorry
