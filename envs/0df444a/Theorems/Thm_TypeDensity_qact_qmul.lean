-- Prove2me | Theorems.Thm_TypeDensity_qact_qmul
-- name    : TypeDensity.qact_qmul
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:51.743723+00:00
-- url     : https://prove2.me/theorems/66f6d558-2103-4385-b72e-0f46dec85c98
-- title:
--   `ρ` is multiplicative: `ρ(U V) = ρ(U) ∘ ρ(V)`.
-- statement:
--   `ρ` is multiplicative: `ρ(U V) = ρ(U) ∘ ρ(V)`.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L718-L744

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

theorem TypeDensity.qact_qmul (U V : QSer) (f : Ser) : qact (qmul U V) f = qact U (qact V f) := by sorry
