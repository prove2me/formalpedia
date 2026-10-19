-- Prove2me | Theorems.Thm_TypeDensity_adic_perturb_congruence_iff
-- name    : TypeDensity.adic_perturb_congruence_iff
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:43.522087+00:00
-- url     : https://prove2.me/theorems/1a458a80-0a97-4f6c-be1e-df7047a78288
-- title:
--   Perturbing by a map that raises adic order preserves and reflects congruence modulo `I^j M`.
-- statement:
--   Perturbing by a map that raises adic order preserves and reflects congruence modulo `I^j M`.
-- source:
--   TypeDensity/Measure/AdicTransport.lean#L83-L106

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
open scoped ENNReal

theorem TypeDensity.adic_perturb_congruence_iff (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (r : M → M) (hr : RaisesAdicOrder I r) (j : ℕ) (x y : M) :
    adicCongr I j (adicPerturb r x) (adicPerturb r y) ↔ adicCongr I j x y := by sorry
