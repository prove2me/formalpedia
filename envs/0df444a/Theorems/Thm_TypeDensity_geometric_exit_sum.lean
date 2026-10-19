-- Prove2me | Theorems.Thm_TypeDensity_geometric_exit_sum
-- name    : TypeDensity.geometric_exit_sum
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:03.583606+00:00
-- url     : https://prove2.me/theorems/f8a47b48-a32e-46fe-9198-4891de1b81bf
-- title:
--   Geometric series with an exit weight: `∑ⱼ λʲ G = G / (1 - λ)` for `0 ≤ λ < 1`.
-- statement:
--   Geometric series with an exit weight: `∑ⱼ λʲ G = G / (1 - λ)` for `0 ≤ λ < 1`.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L857-L862

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

theorem TypeDensity.geometric_exit_sum (lam G : ℝ) (hlam : 0 ≤ lam) (hlam1 : lam < 1) :
    HasSum (fun j : ℕ ↦ lam^j * G) (G / (1 - lam)) := by sorry
