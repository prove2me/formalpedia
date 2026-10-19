-- Prove2me | Theorems.Thm_TypeDensity_state_law_unfold
-- name    : TypeDensity.state_law_unfold
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:15.301916+00:00
-- url     : https://prove2.me/theorems/91cf5902-9d1c-4524-993b-128aa6755622
-- title:
--   Unfolding of the state law: for a single state it is the exit law rescaled by `1 / (1 - returnWeight c)`, and for a crossing state it is the exit law itself.
-- statement:
--   Unfolding of the state law: for a single state it is the exit law rescaled by `1 / (1 - returnWeight c)`, and for a crossing state it is the exit law itself.
-- source:
--   TypeDensity/Formula/StateCombinatorics.lean#L366-L382

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Theorems.Thm_TypeDensity_children_valid
import Theorems.Thm_TypeDensity_nonself_child_rank_lt
import Theorems.Thm_TypeDensity_state_fuel_stable
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

theorem TypeDensity.state_law_unfold (s : State) (hs : s.Valid) (hnt : s.terminal = false) :
    (∀ a c : ℕ, s = State.single a c → stateLaw s =
      lawScale (.inv (.sub (.const 1) (returnWeight c))) (exitLaw s)) ∧
      (∀ a b c h : ℕ, s = State.crossing a b c h → stateLaw s = exitLaw s) := by sorry
