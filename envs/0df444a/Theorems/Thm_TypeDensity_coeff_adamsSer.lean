-- Prove2me | Theorems.Thm_TypeDensity_coeff_adamsSer
-- name    : TypeDensity.coeff_adamsSer
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:11.230385+00:00
-- url     : https://prove2.me/theorems/fbf8d4ec-1d48-4ae5-a4a0-4a3b27a5f68c
-- title:
--   `[xⁿ] ψ_k f = ψ_k([x^{n/k}] f)` if `k ∣ n`, and `0` otherwise (`k ≠ 0`).
-- statement:
--   `[xⁿ] ψ_k f = ψ_k([x^{n/k}] f)` if `k ∣ n`, and `0` otherwise (`k ≠ 0`).
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L345-L349

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
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

theorem TypeDensity.coeff_adamsSer (k : ℕ) (hk : k ≠ 0) (f : Ser) (n : ℕ) :
    PowerSeries.coeff n (adamsSer k f) =
      if k ∣ n then adamsCoef k (PowerSeries.coeff (n / k) f) else 0 := by sorry
