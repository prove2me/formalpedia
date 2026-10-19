-- Prove2me | Theorems.Thm_TypeDensity_coeff_qact_gaussPhi
-- name    : TypeDensity.coeff_qact_gaussPhi
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:50.751253+00:00
-- url     : https://prove2.me/theorems/76d845df-b943-4f87-bf2b-fbacb14d0c31
-- title:
--   Coefficients of `ρ(U)(Φ f)` as a double sum over the total degree `d` and the first contact index `r`.
-- statement:
--   This gives the coefficients of `ρ(U)(Φ f)` as a double sum over the total degree `d` and the first contact index `r`.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L678-L701

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Theorems.Thm_TypeDensity_two_mul_tri
import Theorems.Thm_TypeDensity_qpow_add
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Log
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.coeff_qact_gaussPhi (U : QSer) (f : Ser) (n : ℕ) :
    PowerSeries.coeff n (qact U (gaussPhi f)) = ∑ d ∈ Finset.range (n + 1),
      ∑ r ∈ Finset.range (d + 1),
        qpow (-(tri d : ℤ)) * (U r (n - d) * PowerSeries.coeff (d - r) f) := by sorry
