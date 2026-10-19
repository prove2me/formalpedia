-- Prove2me | Theorems.Thm_TypeDensity_Expr_fraction_snd_ne_zero
-- name    : TypeDensity.Expr.fraction_snd_ne_zero
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:46.159177+00:00
-- url     : https://prove2.me/theorems/220f4c03-1004-43a5-b55f-0ce7525f36be
-- title:
--   A well-formed expression has nonzero denominator.
-- statement:
--   A well-formed expression has nonzero denominator.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L733-L739

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
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
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Log
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.Expr.fraction_snd_ne_zero {x : Expr} (hx : x.wf) : x.fraction.2 ≠ 0 := by sorry
