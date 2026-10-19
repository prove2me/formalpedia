-- Prove2me | Theorems.Thm_TypeDensity_mvPolynomial_zero_null
-- name    : TypeDensity.mvPolynomial_zero_null
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:04.311412+00:00
-- url     : https://prove2.me/theorems/dd40b9bf-618a-4856-b438-21489c24d90e
-- title:
--   The zero set of a nonzero multivariate polynomial over a domain is null for any finite product of copies of an atomless finite measure.
-- statement:
--   The zero set of a nonzero multivariate polynomial over a domain is null for any finite product of copies of an atomless finite measure.
-- source:
--   TypeDensity/Measure/AdicCylinders.lean#L267-L307

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

theorem TypeDensity.mvPolynomial_zero_null {R : Type} [CommRing R] [IsDomain R]
    [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [SecondCountableTopology R]
    [MeasurableSpace R] [BorelSpace R]
    (ν : Measure R) [IsFiniteMeasure ν] [NullSingletonClass ν] :
    ∀ (n : ℕ) (P : MvPolynomial (Fin n) R), P ≠ 0 →
      Measure.pi (fun _ : Fin n => ν) {x | MvPolynomial.eval x P = 0} = 0 := by sorry
