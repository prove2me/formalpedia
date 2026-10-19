-- Prove2me | Theorems.Thm_TypeDensity_adamsSer_logSer
-- name    : TypeDensity.adamsSer_logSer
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:02:25.359168+00:00
-- url     : https://prove2.me/theorems/925a6d98-8b63-46cd-962a-4f34daebde87
-- title:
--   `ψ_k` on series commutes with the logarithm (`k ≠ 0`, `g(0) = 1`).
-- statement:
--   `ψ_k` on series commutes with the logarithm (`k ≠ 0`, `g(0) = 1`).
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L229-L234

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_adamsSer_one
import Theorems.Thm_TypeDensity_adamsSer_sub
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

theorem TypeDensity.adamsSer_logSer (k : ℕ) (hk : k ≠ 0) (g : Ser) (hg : PowerSeries.constantCoeff g = 1) :
    adamsSer k (logSer g) = logSer (adamsSer k g) := by sorry
