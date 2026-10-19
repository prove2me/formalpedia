-- Prove2me | Theorems.Thm_TypeDensity_children_residue_degree_pos
-- name    : TypeDensity.children_residue_degree_pos
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:09.90824+00:00
-- url     : https://prove2.me/theorems/721a7ca2-ac1f-450c-9c18-8bb4f26f5aed
-- title:
--   Every child of a tangent pattern has positive residue degree.
-- statement:
--   Every child of a tangent pattern has positive residue degree.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L221-L232

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
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

theorem TypeDensity.children_residue_degree_pos (s : State) (P : TangentPattern s.degree) (z : ℕ × State)
    (hz : z ∈ children s P) :
    0 < z.1 := by sorry
