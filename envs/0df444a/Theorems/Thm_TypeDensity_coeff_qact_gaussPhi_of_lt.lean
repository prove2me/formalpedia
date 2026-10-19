-- Prove2me | Theorems.Thm_TypeDensity_coeff_qact_gaussPhi_of_lt
-- name    : TypeDensity.coeff_qact_gaussPhi_of_lt
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:02:00.719902+00:00
-- url     : https://prove2.me/theorems/36eb2df9-f985-4f24-beae-232b18640a50
-- title:
--   Leading term: if `f` vanishes below degree `n` and `U₀₀ = 1`, then `[xⁿ] ρ(U)(Φ f) = q^{-tri n} [xⁿ] f`.
-- statement:
--   Leading term: if `f` vanishes below degree `n` and `U₀₀ = 1`, then `[xⁿ] ρ(U)(Φ f) = q^{-tri n} [xⁿ] f`.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L703-L716

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Theorems.Thm_TypeDensity_qpow_zero
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

theorem TypeDensity.coeff_qact_gaussPhi_of_lt (U : QSer) (hU0 : U 0 0 = 1) (f : Ser) (n : ℕ)
    (hf : ∀ m : ℕ, m < n → PowerSeries.coeff m f = 0) :
    PowerSeries.coeff n (qact U (gaussPhi f)) = qpow (-(tri n : ℤ)) * PowerSeries.coeff n f := by sorry
