-- Prove2me | Theorems.Thm_TypeDensity_QCongr_qmul
-- name    : TypeDensity.QCongr.qmul
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:48.605979+00:00
-- url     : https://prove2.me/theorems/1d951f7f-dc40-407f-aa7a-80fd754139bf
-- title:
--   Congruence of contact series is compatible with the twisted product.
-- statement:
--   Congruence of contact series is compatible with the twisted product.
-- source:
--   TypeDensity/Reciprocity/Defs.lean#L777-L782

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

theorem TypeDensity.QCongr.qmul {j : ℕ} {U U' V V' : QSer} (hU : QCongr j U U') (hV : QCongr j V V') :
    QCongr j (qmul U V) (qmul U' V') := by sorry
