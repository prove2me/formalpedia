-- Prove2me | Theorems.Thm_TypeDensity_adamsRat_adamsRat
-- name    : TypeDensity.adamsRat_adamsRat
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:02:01.141053+00:00
-- url     : https://prove2.me/theorems/5a025576-d4a7-4514-8ada-6a0851af8d50
-- title:
--   `ψ_δ ∘ ψ_k = ψ_{δk}` on `ℚ(q)`.
-- statement:
--   `ψ_δ ∘ ψ_k = ψ_{δk}` on `ℚ(q)`.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L321-L329

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Theorems.Thm_TypeDensity_adamsRat_X
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

theorem TypeDensity.adamsRat_adamsRat (δ k : ℕ) (hδ : 0 < δ) (hk : 0 < k) (f : RatFunc ℚ) :
    adamsRat δ (adamsRat k f) = adamsRat (δ * k) f := by sorry
