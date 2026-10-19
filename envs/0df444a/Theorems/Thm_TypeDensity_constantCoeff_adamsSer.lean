-- Prove2me | Theorems.Thm_TypeDensity_constantCoeff_adamsSer
-- name    : TypeDensity.constantCoeff_adamsSer
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:46.877186+00:00
-- url     : https://prove2.me/theorems/515e76ad-2803-4857-bd95-7fa92dd7f064
-- title:
--   The constant term of `ψ_k f` is `ψ_k` of the constant term of `f` (`k ≠ 0`).
-- statement:
--   The constant term of `ψ_k f` is `ψ_k` of the constant term of `f` (`k ≠ 0`).
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L351-L354

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Theorems.Thm_TypeDensity_coeff_adamsSer
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

theorem TypeDensity.constantCoeff_adamsSer (k : ℕ) (hk : k ≠ 0) (f : Ser) :
    PowerSeries.constantCoeff (adamsSer k f) = adamsCoef k (PowerSeries.constantCoeff f) := by sorry
