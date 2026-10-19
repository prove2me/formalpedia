-- Prove2me | Theorems.Thm_TypeDensity_lawCoef_lawProd
-- name    : TypeDensity.lawCoef_lawProd
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:49.941994+00:00
-- url     : https://prove2.me/theorems/507a6c2a-0eac-4eba-b31b-440e43fa3430
-- title:
--   `lawCoef` is multiplicative on finite products `lawProd`.
-- statement:
--   `lawCoef` is multiplicative on finite products `lawProd`.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L867-L869

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_lawInterp_lawProd
import Theorems.Thm_TypeDensity_Expr_rational_mul
import Theorems.Thm_TypeDensity_Expr_rational_const
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

theorem TypeDensity.lawCoef_lawProd (Ls : List Law) : lawCoef (lawProd Ls) = (Ls.map lawCoef).prod := by sorry
