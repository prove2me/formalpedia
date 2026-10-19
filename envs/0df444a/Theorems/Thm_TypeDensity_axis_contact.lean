-- Prove2me | Theorems.Thm_TypeDensity_axis_contact
-- name    : TypeDensity.axis_contact
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:04.017979+00:00
-- url     : https://prove2.me/theorems/0d4a275d-891a-480d-bdfd-766fc394a05c
-- title:
--   Let `Xₛ` be a variable dividing `T^a X^b`.
-- statement:
--   Let `Xₛ` be a variable dividing `T^a X^b`. If the images of `F` and `Xₛ` in the special fibre `k[[T,X]]/(T^a X^b)` have finite contact `c`, then `Xₛ` is a nonzerodivisor modulo `F` and `k[[T,X]]/(F, Xₛⁿ)` has length `n c`.
-- source:
--   TypeDensity/Unramified/LocalDescent.lean#L35-L62

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Theorems.Thm_TypeDensity_axis_quotient_length_top
import Theorems.Thm_TypeDensity_axis_pow_mul_mem_span_cancel
import Theorems.Thm_TypeDensity_length_double_quotient_eq
import Theorems.Thm_TypeDensity_length_quotient_sup_pow_eq_mul
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Completeness
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.axis_contact (k : Type) [Field k] (a b : ℕ) (F : TwoSeries k) (s t : Fin 2)
    (hst : s ≠ t) (c : ℕ)
    (hdvd : (MvPowerSeries.X s : TwoSeries k) ∣ MvPowerSeries.X 0 ^ a * MvPowerSeries.X 1 ^ b)
    (hc : contact (Ideal.Quotient.mk (monomialIdeal k a b) F)
      (Ideal.Quotient.mk _ (MvPowerSeries.X s)) = c) :
    (∀ n x, (MvPowerSeries.X s : TwoSeries k) ^ n * x ∈ Ideal.span {F} → x ∈ Ideal.span {F}) ∧
    ∀ n : ℕ, Module.length (TwoSeries k) (TwoSeries k ⧸
      (Ideal.span {F} ⊔ Ideal.span {(MvPowerSeries.X s : TwoSeries k) ^ n})) = n * c := by sorry
