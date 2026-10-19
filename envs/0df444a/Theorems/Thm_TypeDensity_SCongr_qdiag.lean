-- Prove2me | Theorems.Thm_TypeDensity_SCongr_qdiag
-- name    : TypeDensity.SCongr.qdiag
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:44.239547+00:00
-- url     : https://prove2.me/theorems/c27ecbff-2abf-4f3f-9fca-54b490ace539
-- title:
--   Diagonal substitution doubles the congruence degree: `f ≡ g` through `M` gives `qdiag f ≡ qdiag g` through `2M + 1`.
-- statement:
--   Diagonal substitution doubles the congruence degree: `f ≡ g` through `M` gives `qdiag f ≡ qdiag g` through `2M + 1`.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L784-L792

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

theorem TypeDensity.SCongr.qdiag {M : ℕ} {f g : Ser} (h : SCongr M f g) :
    QCongr (2 * M + 1) (qdiag f) (qdiag g) := by sorry
