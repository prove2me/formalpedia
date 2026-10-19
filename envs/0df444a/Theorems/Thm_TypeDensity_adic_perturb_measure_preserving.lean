-- Prove2me | Theorems.Thm_TypeDensity_adic_perturb_measure_preserving
-- name    : TypeDensity.adic_perturb_measure_preserving
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:43:58.479981+00:00
-- url     : https://prove2.me/theorems/318311bd-940c-4a8e-98af-e3c407468048
-- title:
--   An adic perturbation preserves an invariant probability measure with finite adic quotients.
-- statement:
--   An adic perturbation preserves an invariant probability measure with finite adic quotients.
-- source:
--   TypeDensity/Measure/AdicTransport.lean#L265-L303

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Theorems.Thm_TypeDensity_adic_perturb_cylinder_preimage
import Theorems.Thm_TypeDensity_adic_perturb_measurable
import Theorems.Thm_TypeDensity_finite_measures_from_cylinders
import Theorems.Thm_TypeDensity_finite_quotient_fiber_mass
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
open scoped ENNReal

theorem TypeDensity.adic_perturb_measure_preserving (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (r : M → M) (hr : RaisesAdicOrder I r) [IsAdicComplete I M] [MeasurableSpace M]
    [MeasurableAdd M] (mu : MeasureTheory.Measure M) [MeasureTheory.IsProbabilityMeasure mu]
    [MeasureTheory.Measure.IsAddLeftInvariant mu] (hgen : ‹MeasurableSpace M› = adicCylinderSpace I
    M) (hfinite : ∀ j, Finite (AdicQuotient I M j)) :
    MeasureTheory.MeasurePreserving (adicPerturb r) mu mu := by sorry
