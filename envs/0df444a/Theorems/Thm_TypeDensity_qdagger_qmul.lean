-- Prove2me | Theorems.Thm_TypeDensity_qdagger_qmul
-- name    : TypeDensity.qdagger_qmul
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:46.403905+00:00
-- url     : https://prove2.me/theorems/68d15868-7f1e-478e-bf59-67053ef34984
-- title:
--   `†` is an anti-homomorphism of the twisted product.
-- statement:
--   `†` is an anti-homomorphism of the twisted product.
-- source:
--   TypeDensity/Reciprocity/Quantum.lean#L451-L470

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_qpow_add
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

theorem TypeDensity.qdagger_qmul (U V : QSer) : qdagger (qmul U V) = qmul (qdagger V) (qdagger U) := by sorry
