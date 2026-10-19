-- Prove2me | Theorems.Thm_TypeDensity_child_volume_ratio
-- name    : TypeDensity.child_volume_ratio
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:49.810006+00:00
-- url     : https://prove2.me/theorems/f595fca3-7b66-417c-9de1-d96ab0cbaf5d
-- title:
--   The volume recursion: the children of an allowed tangent pattern `P` at a state `s`, weighted by `q^(-tri d)`, have total volume `divisorProbability s d · stateVolume s`.
-- statement:
--   The volume recursion: the children of an allowed tangent pattern `P` at a state `s`, weighted by `q^(-tri d)`, have total volume `divisorProbability s d · stateVolume s`.
-- source:
--   TypeDensity/Measure/AdicCylinders.lean#L342-L399

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
set_option autoImplicit false

open TypeDensity
open MeasureTheory
open scoped BigOperators ENNReal

theorem TypeDensity.child_volume_ratio (s : State) (hs : s.Valid) (P : TangentPattern s.degree)
    (hP : Allowed s P) (q : ℕ) (hq : 2 ≤ q) :
    ((q:ℚ)⁻¹^(tri P.d.val))
        * (((children s P).map fun z => (stateVolume z.2).eval ((q:ℚ)^z.1)).prod)
      / (stateVolume s).eval q = (divisorProbability s P.d.val).eval q := by sorry
