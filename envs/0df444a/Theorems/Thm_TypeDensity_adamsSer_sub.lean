-- Prove2me | Theorems.Thm_TypeDensity_adamsSer_sub
-- name    : TypeDensity.adamsSer_sub
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:10.001121+00:00
-- url     : https://prove2.me/theorems/53647d3d-4461-4dfb-922d-c49f956e4b5d
-- title:
--   `ψ_k` on series is additive on differences (`k ≠ 0`).
-- statement:
--   `ψ_k` on series is additive on differences (`k ≠ 0`).
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L360-L363

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

theorem TypeDensity.adamsSer_sub (k : ℕ) (hk : k ≠ 0) (f g : Ser) :
    adamsSer k (f - g) = adamsSer k f - adamsSer k g := by sorry
