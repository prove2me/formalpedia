-- Prove2me | Theorems.Thm_TypeDensity_mvPowerSeries_fin_two_quotient_var_regular_mod_var
-- name    : TypeDensity.mvPowerSeries_fin_two_quotient_var_regular_mod_var
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:50.785421+00:00
-- url     : https://prove2.me/theorems/786d9576-f2f5-4851-8470-8bf308705b04
-- title:
--   If `P` has nonzero constant coefficient over a domain, then `X t` is a nonzerodivisor modulo `(P, X s)` for `s ≠ t`.
-- statement:
--   If `P` has nonzero constant coefficient over a domain, then `X t` is a nonzerodivisor modulo `(P, X s)` for `s ≠ t`.
-- source:
--   TypeDensity/Surfaces/PowerSeries.lean#L188-L237

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

theorem TypeDensity.mvPowerSeries_fin_two_quotient_var_regular_mod_var (A : Type) [CommRing A] [IsDomain A]
    (s t : Fin 2) (hst : s ≠ t) (P : MvPowerSeries (Fin 2) A)
    (hP : MvPowerSeries.constantCoeff P ≠ 0) :
    Function.Injective
    (fun g : (MvPowerSeries (Fin 2) A ⧸ Ideal.span {P}) ⧸ Ideal.span
      {Ideal.Quotient.mk (Ideal.span {P}) (MvPowerSeries.X s)} => Ideal.Quotient.mk
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {P}) (MvPowerSeries.X s)})
      (Ideal.Quotient.mk (Ideal.span {P}) (MvPowerSeries.X t)) * g) := by sorry
