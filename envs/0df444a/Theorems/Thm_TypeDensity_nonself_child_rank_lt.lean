-- Prove2me | Theorems.Thm_TypeDensity_nonself_child_rank_lt
-- name    : TypeDensity.nonself_child_rank_lt
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:14.30828+00:00
-- url     : https://prove2.me/theorems/cd28e6a5-9f93-4b68-8e0f-e9aa9af97480
-- title:
--   Every child of a non-self allowed pattern has strictly smaller rank than its parent.
-- statement:
--   Every child of a non-self allowed pattern has strictly smaller rank than its parent.
-- source:
--   TypeDensity/Formula/StateCombinatorics.lean#L254-L293

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Theorems.Thm_TypeDensity_children_degree_identity
import Theorems.Thm_TypeDensity_children_residue_degree_pos
import Theorems.Thm_TypeDensity_child_degree_le
import Theorems.Thm_TypeDensity_children_valid
import Theorems.Thm_TypeDensity_rank_lt_of_degree_lt
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

theorem TypeDensity.nonself_child_rank_lt (s : State) (hs : s.Valid) (P : TangentPattern s.degree)
    (hP : Allowed s P) (hself : ¬ SelfPattern s P) (z : ℕ × State) (hz : z ∈ children s P) :
    z.2.rank < s.rank := by sorry
