-- Prove2me | Theorems.Thm_TypeDensity_recipSer_qact
-- name    : TypeDensity.recipSer_qact
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:46.95278+00:00
-- url     : https://prove2.me/theorems/0742a4e4-16c6-44ca-bcaa-050113352a29
-- title:
--   Conjugating `ρ(U)` by the reciprocal substitution gives `ρ̄(v U)`.
-- statement:
--   Conjugating `ρ(U)` by the reciprocal substitution gives `ρ̄(v U)`.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L442-L449

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_recipRat_X
import Theorems.Thm_TypeDensity_recipCoef_scalar
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

theorem TypeDensity.recipSer_qact (U : QSer) (f : Ser) :
    recipSer (qact U f) = qactRecip (qrecip U) (recipSer f) := by sorry
