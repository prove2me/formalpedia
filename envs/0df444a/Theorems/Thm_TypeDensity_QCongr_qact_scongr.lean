-- Prove2me | Theorems.Thm_TypeDensity_QCongr_qact_scongr
-- name    : TypeDensity.QCongr.qact_scongr
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:54.289107+00:00
-- url     : https://prove2.me/theorems/4c9d118c-b915-49ba-b36d-cfa90d2840a0
-- title:
--   If `U ≡ V` through total degree `n`, then `ρ(U) f ≡ ρ(V) f` through degree `n`.
-- statement:
--   If `U ≡ V` through total degree `n`, then `ρ(U) f ≡ ρ(V) f` through degree `n`.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L670-L676

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

theorem TypeDensity.QCongr.qact_scongr {n : ℕ} {U V : QSer} (hUV : QCongr n U V) (f : Ser) :
    SCongr n (qact U f) (qact V f) := by sorry
