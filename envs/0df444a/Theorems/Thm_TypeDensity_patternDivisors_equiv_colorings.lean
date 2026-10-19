-- Prove2me | Theorems.Thm_TypeDensity_patternDivisors_equiv_colorings
-- name    : TypeDensity.patternDivisors_equiv_colorings
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:15.461017+00:00
-- url     : https://prove2.me/theorems/af4d2de0-fbbe-4db5-aec4-68f3e34c6e19
-- title:
--   Over a finite field, the exceptional divisors with tangent pattern `P` are in bijection with tuples, indexed by degrees `i + 1`, of colorings of the nonboundary directions of that degree by `Fin s.deg
-- statement:
--   Over a finite field, the exceptional divisors with tangent pattern `P` are in bijection with tuples, indexed by degrees `i + 1`, of colorings of the nonboundary directions of that degree by `Fin s.degree ⊕ none` with color counts `P.other (i, j)`.
-- source:
--   TypeDensity/Formula/PatternCounts.lean#L494-L507

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

theorem TypeDensity.patternDivisors_equiv_colorings (k : Type) [Field k] [Finite k] (s : State)
    (P : TangentPattern s.degree) (hP : P.rt.val + P.rx.val + patternWeight P.other = P.d.val)
    (hrx : ∀ a c, s = State.single a c → P.rx.val = 0) :
    Nonempty (patternDivisors k s P ≃ ∀ i : Fin s.degree,
      {f : {Q : ClosedDirection k // Q ∉ boundaryDirections k s ∧
          directionDegree k Q = i.val + 1} → Option (Fin s.degree) //
        ∀ j : Fin s.degree, Nat.card {Q // f Q = some j} = (P.other (i, j)).val}) := by sorry
