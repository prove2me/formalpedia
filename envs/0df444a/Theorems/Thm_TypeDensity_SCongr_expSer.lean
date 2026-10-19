-- Prove2me | Theorems.Thm_TypeDensity_SCongr_expSer
-- name    : TypeDensity.SCongr.expSer
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:02:22.700947+00:00
-- url     : https://prove2.me/theorems/24fba571-e6e3-4d9c-a059-e972803f1edf
-- title:
--   `exp` preserves congruence through degree `n` (on series with zero constant term).
-- statement:
--   `exp` preserves congruence through degree `n` (on series with zero constant term).
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L907-L911

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_scongr_subst
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

theorem TypeDensity.SCongr.expSer {n : ℕ} {f g : Ser} (hf : PowerSeries.constantCoeff f = 0)
    (hg : PowerSeries.constantCoeff g = 0) (h : SCongr n f g) :
    SCongr n (TypeDensity.expSer f) (TypeDensity.expSer g) := by sorry
