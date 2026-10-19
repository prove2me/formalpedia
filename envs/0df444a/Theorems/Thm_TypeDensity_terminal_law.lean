-- Prove2me | Theorems.Thm_TypeDensity_terminal_law
-- name    : TypeDensity.terminal_law
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:46.298588+00:00
-- url     : https://prove2.me/theorems/fdd62fc4-5838-410c-9fdf-9810e1568358
-- title:
--   The law of the terminal state `S(a;
-- statement:
--   The law of the terminal state `S(a; 1)` is the atom `[(a, 1)]`.
-- source:
--   TypeDensity/Formula/StateCombinatorics.lean#L391-L394

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

theorem TypeDensity.terminal_law (a : ℕ) :
    stateLaw (State.single a 1) = lawAtom a 1 := by sorry
