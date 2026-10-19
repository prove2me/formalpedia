-- Prove2me | Theorems.Thm_TypeDensity_adic_perturb_cylinder_preimage
-- name    : TypeDensity.adic_perturb_cylinder_preimage
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:05.317144+00:00
-- url     : https://prove2.me/theorems/a0be50b8-5d55-450d-ba4b-de45383bdbb9
-- title:
--   The preimage of an adic cylinder under an adic perturbation is an adic cylinder.
-- statement:
--   The preimage of an adic cylinder under an adic perturbation is an adic cylinder.
-- source:
--   TypeDensity/Measure/AdicTransport.lean#L192-L203

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Theorems.Thm_TypeDensity_adic_perturb_congruence_iff
import Theorems.Thm_TypeDensity_adic_perturb_bijective
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

theorem TypeDensity.adic_perturb_cylinder_preimage (R M : Type) [CommRing R] [AddCommGroup M]
    [Module R M]
    (I : Ideal R) (r : M → M) (hr : RaisesAdicOrder I r) [IsAdicComplete I M] (j : ℕ) (z : M) :
    ∃ x : M, adicPerturb r x = z ∧ (adicPerturb r) ⁻¹' {w | adicCongr I j w z} =
        {y | adicCongr I j y x} := by sorry
