-- Prove2me | Theorems.Thm_TypeDensity_qdiag_mul
-- name    : TypeDensity.qdiag_mul
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:20:08.743402+00:00
-- url     : https://prove2.me/theorems/98df9d8d-357d-4ed7-85fe-fe06cfa5c6da
-- title:
--   Diagonal substitution `x ↦ E_{1,1}` is multiplicative into the quantum torus.
-- statement:
--   Diagonal substitution `x ↦ E_{1,1}` is multiplicative into the quantum torus.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L738-L767

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_chooseTwo_add
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

theorem TypeDensity.qdiag_mul (f g : Ser) : qdiag (f * g) = qmul (qdiag f) (qdiag g) := by sorry
