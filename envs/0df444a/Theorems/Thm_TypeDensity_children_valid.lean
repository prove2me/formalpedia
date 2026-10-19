-- Prove2me | Theorems.Thm_TypeDensity_children_valid
-- name    : TypeDensity.children_valid
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:39.146331+00:00
-- url     : https://prove2.me/theorems/71df5258-dda0-42ba-9636-3da825dc9f7d
-- title:
--   Children of an allowed pattern on a valid state are valid states.
-- statement:
--   Children of an allowed pattern on a valid state are valid states.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L244-L280

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

theorem TypeDensity.children_valid (s : State) (hs : s.Valid) (P : TangentPattern s.degree)
    (hP : Allowed s P) (z : ℕ × State) (hz : z ∈ children s P) :
    z.2.Valid := by sorry
