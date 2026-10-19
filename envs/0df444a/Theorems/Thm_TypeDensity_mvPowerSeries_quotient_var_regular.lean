-- Prove2me | Theorems.Thm_TypeDensity_mvPowerSeries_quotient_var_regular
-- name    : TypeDensity.mvPowerSeries_quotient_var_regular
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:04.455619+00:00
-- url     : https://prove2.me/theorems/77ced902-63a0-4333-a1b6-9adbecb2c639
-- title:
--   If `P` has nonzero constant coefficient over a domain, then `X s` is a nonzerodivisor modulo `P`.
-- statement:
--   If `P` has nonzero constant coefficient over a domain, then `X s` is a nonzerodivisor modulo `P`.
-- source:
--   TypeDensity/Surfaces/PowerSeries.lean#L158-L175

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
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
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.mvPowerSeries_quotient_var_regular (σ A : Type) [CommRing A] [IsDomain A] (s : σ)
    (P : MvPowerSeries σ A) (hP : MvPowerSeries.constantCoeff P ≠ 0) :
    Function.Injective
    (fun g : MvPowerSeries σ A ⧸ Ideal.span {P} ↦ Ideal.Quotient.mk (Ideal.span {P})
      (MvPowerSeries.X s) * g) := by sorry
