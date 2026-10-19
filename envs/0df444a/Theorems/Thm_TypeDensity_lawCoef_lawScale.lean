-- Prove2me | Theorems.Thm_TypeDensity_lawCoef_lawScale
-- name    : TypeDensity.lawCoef_lawScale
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:56.808323+00:00
-- url     : https://prove2.me/theorems/4654f587-e981-471b-9e91-496a1da5d101
-- title:
--   `lawCoef` turns `lawScale x` into multiplication by the scalar `x.rational`.
-- statement:
--   `lawCoef` turns `lawScale x` into multiplication by the scalar `x.rational`.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L771-L774

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_lawInterp_lawScale
import Theorems.Thm_TypeDensity_Expr_rational_mul
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

theorem TypeDensity.lawCoef_lawScale (x : Expr) (L : Law) :
    lawCoef (lawScale x L) = scalar x.rational * lawCoef L := by sorry
