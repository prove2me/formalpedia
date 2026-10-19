-- Prove2me | Theorems.Thm_TypeDensity_adic_perturb_bijective
-- name    : TypeDensity.adic_perturb_bijective
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:41.887706+00:00
-- url     : https://prove2.me/theorems/2ec7330e-e3d5-4cd0-8819-887c9d812751
-- title:
--   On an `I`-adically complete module, `x ↦ x + r x` is bijective when `r` raises adic order.
-- statement:
--   On an `I`-adically complete module, `x ↦ x + r x` is bijective when `r` raises adic order.
-- source:
--   TypeDensity/Measure/AdicTransport.lean#L179-L190

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Theorems.Thm_TypeDensity_adic_congruence_rules
import Theorems.Thm_TypeDensity_adic_perturb_congruence_iff
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

theorem TypeDensity.adic_perturb_bijective (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
    (r : M → M) (hr : RaisesAdicOrder I r) [IsAdicComplete I M] :
    Function.Bijective (adicPerturb r) := by sorry
