-- Prove2me | Theorems.Thm_TypeDensity_coeff_dilate
-- name    : TypeDensity.coeff_dilate
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:58.660656+00:00
-- url     : https://prove2.me/theorems/63faa733-f970-43e5-b49b-1b6d2ba2d672
-- title:
--   `[xⁿ] S f = qⁿ [xⁿ] f`.
-- statement:
--   `[xⁿ] S f = qⁿ [xⁿ] f`.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L602-L605

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
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

theorem TypeDensity.coeff_dilate (f : Ser) (n : ℕ) :
    PowerSeries.coeff n (dilate f) = qpow (n : ℤ) * PowerSeries.coeff n f := by sorry
