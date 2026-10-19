-- Prove2me | Theorems.Thm_TypeDensity_coprime_of_monic_reduction_one
-- name    : TypeDensity.coprime_of_monic_reduction_one
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:02.552902+00:00
-- url     : https://prove2.me/theorems/cdd9c10e-152f-4f13-954a-1182b112f1d0
-- title:
--   Over a discrete valuation ring `R` with fraction field `K`, a monic polynomial `A` and a polynomial `B` reducing to `1` modulo the maximal ideal are coprime over `K`.
-- statement:
--   Over a discrete valuation ring `R` with fraction field `K`, a monic polynomial `A` and a polynomial `B` reducing to `1` modulo the maximal ideal are coprime over `K`.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L756-L795

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
open Polynomial

theorem TypeDensity.coprime_of_monic_reduction_one (R K : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A B : Polynomial R)
    (hA : A.Monic) (hB : B.map (IsLocalRing.residue R) = 1) :
    IsCoprime (A.map (algebraMap R K)) (B.map (algebraMap R K)) := by sorry
