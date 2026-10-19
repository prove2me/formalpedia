-- Prove2me | Theorems.Thm_TypeDensity_local_law_safe
-- name    : TypeDensity.local_law_safe
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:11.340744+00:00
-- url     : https://prove2.me/theorems/70938967-8463-4230-960a-d93b6e523a3f
-- title:
--   The local law of every valid state is safe.
-- statement:
--   The local law of every valid state is safe.
-- source:
--   TypeDensity/Formula/StateCombinatorics.lean#L499-L537

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Theorems.Thm_TypeDensity_expression_pow_safe
import Theorems.Thm_TypeDensity_children_residue_degree_pos
import Theorems.Thm_TypeDensity_children_valid
import Theorems.Thm_TypeDensity_divisor_count_safe
import Theorems.Thm_TypeDensity_divisor_probability_safe
import Theorems.Thm_TypeDensity_law_safe_descend
import Theorems.Thm_TypeDensity_law_safe_mul
import Theorems.Thm_TypeDensity_law_safe_scale
import Theorems.Thm_TypeDensity_nonself_child_rank_lt
import Theorems.Thm_TypeDensity_state_fuel_stable
import Theorems.Thm_TypeDensity_return_weight_bounds
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

theorem TypeDensity.local_law_safe (s : State) (hs : s.Valid) :
    LawSafe (stateLaw s) := by sorry
