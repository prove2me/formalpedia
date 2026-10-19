-- Prove2me | Theorems.Thm_TypeDensity_adic_perturb_measurable
-- name    : TypeDensity.adic_perturb_measurable
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:13.76298+00:00
-- url     : https://prove2.me/theorems/89c2a9b0-de71-4889-a7ec-2bfb05e13359
-- title:
--   An adic perturbation is measurable for the adic cylinder σ-algebra.
-- statement:
--   An adic perturbation is measurable for the adic cylinder σ-algebra.
-- source:
--   TypeDensity/Measure/AdicTransport.lean#L205-L218

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Theorems.Thm_TypeDensity_adic_perturb_cylinder_preimage
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

theorem TypeDensity.adic_perturb_measurable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (r : M → M) (hr : RaisesAdicOrder I r) [IsAdicComplete I M] [MeasurableSpace M]
    (hgen : ‹MeasurableSpace M› = adicCylinderSpace I M) :
    Measurable (adicPerturb r) := by sorry
