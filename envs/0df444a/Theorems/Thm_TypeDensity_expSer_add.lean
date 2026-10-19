-- Prove2me | Theorems.Thm_TypeDensity_expSer_add
-- name    : TypeDensity.expSer_add
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:46.801984+00:00
-- url     : https://prove2.me/theorems/eaf4c772-77b5-4855-9375-cbf5c36d5253
-- title:
--   The exponential is additive-to-multiplicative on series with zero constant term.
-- statement:
--   The exponential is additive-to-multiplicative on series with zero constant term.
-- source:
--   TypeDensity/Reciprocity/Plethysm.lean#L131-L143

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Theorems.Thm_TypeDensity_constantCoeff_expSer
import Theorems.Thm_TypeDensity_derivative_expSer
import Theorems.Thm_TypeDensity_eq_of_mul_derivative_eq_mul
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

theorem TypeDensity.expSer_add (f g : Ser) (hf : PowerSeries.constantCoeff f = 0)
    (hg : PowerSeries.constantCoeff g = 0) :
    expSer (f + g) = expSer f * expSer g := by sorry
