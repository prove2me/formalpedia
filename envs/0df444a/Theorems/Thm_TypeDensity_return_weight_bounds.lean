-- Prove2me | Theorems.Thm_TypeDensity_return_weight_bounds
-- name    : TypeDensity.return_weight_bounds
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:15.233129+00:00
-- url     : https://prove2.me/theorems/dbaaebd8-514f-45a7-81f1-fb37b1d14b46
-- title:
--   For `q, c ≥ 2`, the return weight `q · q^(-tri c)` lies in `(0, q⁻²]`, in particular below `1`.
-- statement:
--   For `q, c ≥ 2`, the return weight `q · q^(-tri c)` lies in `(0, q⁻²]`, in particular below `1`.
-- source:
--   TypeDensity/Formula/StateCombinatorics.lean#L414-L433

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

theorem TypeDensity.return_weight_bounds (q c : ℕ) (hq : 2 ≤ q) (hc : 2 ≤ c) :
    0 < (returnWeight c).eval q ∧ (returnWeight c).eval q ≤ (q : ℚ)⁻¹^2 ∧
      (returnWeight c).eval q < 1 := by sorry
