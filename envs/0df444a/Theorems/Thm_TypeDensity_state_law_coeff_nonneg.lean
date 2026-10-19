-- Prove2me | Theorems.Thm_TypeDensity_state_law_coeff_nonneg
-- name    : TypeDensity.state_law_coeff_nonneg
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:32.473157+00:00
-- url     : https://prove2.me/theorems/3f59fafa-c433-48e1-ad9b-2719f2137546
-- title:
--   At a prime power `Q`, the coefficients of the law of a valid state, and of all its descents, are nonnegative.
-- statement:
--   At a prime power `Q`, the coefficients of the law of a valid state, and of all its descents, are nonnegative.
-- source:
--   TypeDensity/Formula/PatternCounts.lean#L614-L622

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Formula_FiniteFieldCounts
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Formula_PatternCounts
import Theorems.Thm_TypeDensity_prime_power_ge_two
import Theorems.Thm_TypeDensity_children_residue_degree_pos
import Theorems.Thm_TypeDensity_children_valid
import Theorems.Thm_TypeDensity_law_coeff_nonneg_closure
import Theorems.Thm_TypeDensity_tangent_count_nonneg
import Theorems.Thm_TypeDensity_divisor_probability_pos
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.state_law_coeff_nonneg (Q : ℕ) (hQ : PrimePower Q) (s : State) (hs : s.Valid)
    (σ : FactorType) :
    0 ≤ (lawCoeff (stateLaw s) σ).eval Q ∧
      ∀ δ : ℕ, 0 < δ → 0 ≤ (lawCoeff (lawDescend δ (stateLaw s)) σ).eval Q := by sorry
