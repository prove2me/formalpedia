-- Prove2me | Theorems.Thm_TypeDensity_law_safe_scale
-- name    : TypeDensity.law_safe_scale
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:15.637458+00:00
-- url     : https://prove2.me/theorems/91f3121a-79b9-443a-b297-ea6fbc7e39f8
-- title:
--   Scaling a safe law by an everywhere-safe expression gives a safe law.
-- statement:
--   Scaling a safe law by an everywhere-safe expression gives a safe law.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L719-L725

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

theorem TypeDensity.law_safe_scale (x : Expr) (L : Law) (hx : x.allSafe) (hL : LawSafe L) :
    LawSafe (lawScale x L) := by sorry
