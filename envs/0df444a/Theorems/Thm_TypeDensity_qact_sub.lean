-- Prove2me | Theorems.Thm_TypeDensity_qact_sub
-- name    : TypeDensity.qact_sub
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:49.858003+00:00
-- url     : https://prove2.me/theorems/585772a5-095d-4d5b-91af-591571b5f605
-- title:
--   `ρ(U)` is additive on differences.
-- statement:
--   `ρ(U)` is additive on differences.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L761-L764

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

theorem TypeDensity.qact_sub (U : QSer) (f g : Ser) : qact U (f - g) = qact U f - qact U g := by sorry
