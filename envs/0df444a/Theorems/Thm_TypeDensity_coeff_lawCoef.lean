-- Prove2me | Theorems.Thm_TypeDensity_coeff_lawCoef
-- name    : TypeDensity.coeff_lawCoef
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:33:01.905991+00:00
-- url     : https://prove2.me/theorems/26ab11d6-c5fb-4e92-b587-98a10648439e
-- title:
--   For a well-formed law, the `σ`-coefficient of `lawCoef L` is the rational function of `lawCoeff L σ`.
-- statement:
--   For a well-formed law, the `σ`-coefficient of `lawCoef L` is the rational function of `lawCoeff L σ`.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L995-L1019

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_Expr_rational_const
import Theorems.Thm_TypeDensity_Expr_rational_sum
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

theorem TypeDensity.coeff_lawCoef (L : Law) (hL : LawWf L) (σ : FactorType) :
    (lawCoef L).coeff σ = (lawCoeff L σ).rational := by sorry
