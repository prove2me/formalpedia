-- Prove2me | Theorems.Thm_TypeDensity_contact_fiberX_eq_axisQuotientLength
-- name    : TypeDensity.contact_fiberX_eq_axisQuotientLength
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:05.769572+00:00
-- url     : https://prove2.me/theorems/ca241237-8f47-45ef-a678-07204cfc720d
-- title:
--   On the special fibre `k⟦T, X⟧ ⧸ (T^a X^b)` with `0 < b`, the contact of `F` with `X` is `ℓ(k⟦T, X⟧ ⧸ (F, X))`.
-- statement:
--   On the special fibre `k⟦T, X⟧ ⧸ (T^a X^b)` with `0 < b`, the contact of `F` with `X` is `ℓ(k⟦T, X⟧ ⧸ (F, X))`.
-- source:
--   TypeDensity/Surfaces/TruncatedSeries.lean#L170-L182

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Surfaces_TruncatedSeries
import Theorems.Thm_TypeDensity_length_double_quotient_eq
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

theorem TypeDensity.contact_fiberX_eq_axisQuotientLength (k : Type) [Field k] (a b : ℕ) (hb : 0 < b)
    (F : TwoSeries k) :
    contact (Ideal.Quotient.mk (monomialIdeal k a b) F) (fiberX k a b) =
      axisQuotientLength k 1 F := by sorry
