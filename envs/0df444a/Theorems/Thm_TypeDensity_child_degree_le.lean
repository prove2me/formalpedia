-- Prove2me | Theorems.Thm_TypeDensity_child_degree_le
-- name    : TypeDensity.child_degree_le
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:44.321877+00:00
-- url     : https://prove2.me/theorems/1ddf902d-6a9f-4143-8b77-c458338708b1
-- title:
--   Each child of an allowed pattern has degree at most that of the parent state.
-- statement:
--   Each child of an allowed pattern has degree at most that of the parent state.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L234-L242

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Theorems.Thm_TypeDensity_children_degree_identity
import Theorems.Thm_TypeDensity_children_residue_degree_pos
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

theorem TypeDensity.child_degree_le (s : State) (hs : s.Valid) (P : TangentPattern s.degree)
    (hP : Allowed s P) (z : ℕ × State) (hz : z ∈ children s P) :
    z.2.degree ≤ s.degree := by sorry
