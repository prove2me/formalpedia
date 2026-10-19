-- Prove2me | Theorems.Thm_TypeDensity_list_get_fiber_card
-- name    : TypeDensity.list_get_fiber_card
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:07.016986+00:00
-- url     : https://prove2.me/theorems/c13ddfdd-f145-4a2c-82c1-6d36c3effa27
-- title:
--   The number of positions at which a list takes the value `x` is `l.count x`.
-- statement:
--   The number of positions at which a list takes the value `x` is `l.count x`.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L877-L900

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

theorem TypeDensity.list_get_fiber_card (α : Type) [DecidableEq α] (l : List α) (x : α) :
    Nat.card {j : Fin l.length // l.get j = x} = l.count x := by sorry
