-- Prove2me | Theorems.Thm_TypeDensity_HasPolynomialTypeF_to_original
-- name    : TypeDensity.HasPolynomialTypeF.to_original
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:04.174392+00:00
-- url     : https://prove2.me/theorems/87ca2ec5-4aac-40e9-b3b9-ec9410e6a7d2
-- title:
--   A route-F polynomial type is a polynomial type (forget the closure-finiteness witnesses).
-- statement:
--   A route-F polynomial type is a polynomial type (forget the closure-finiteness witnesses).
-- source:
--   TypeDensity/Algebra/AlgebraType.lean#L344-L348

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
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
import Mathlib.RingTheory.Henselian
set_option autoImplicit false

open TypeDensity
open scoped TensorProduct
open Polynomial IsLocalRing

theorem TypeDensity.HasPolynomialTypeF.to_original {O : Type} [CommRing O] [IsDomain O]
    {F : (BaseField O)[X]} {σ : FactorType} (h : HasPolynomialTypeF O F σ) :
    HasPolynomialType O F σ := by sorry
