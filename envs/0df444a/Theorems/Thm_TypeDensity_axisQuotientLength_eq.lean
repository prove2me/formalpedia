-- Prove2me | Theorems.Thm_TypeDensity_axisQuotientLength_eq
-- name    : TypeDensity.axisQuotientLength_eq
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:03.465985+00:00
-- url     : https://prove2.me/theorems/8b41c30b-fcf9-40e3-8e66-f8c488427c0b
-- title:
--   If the restriction of `F` to the axis `X_t` has order `d`, then `ℓ(k⟦T, X⟧ ⧸ (F, X_s)) = d`.
-- statement:
--   If the restriction of `F` to the axis `X_t` has order `d`, then `ℓ(k⟦T, X⟧ ⧸ (F, X_s)) = d`.
-- source:
--   TypeDensity/Surfaces/TruncatedSeries.lean#L79-L137

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Surfaces_TruncatedSeries
import Theorems.Thm_TypeDensity_axis_pow_mul_mem_span_cancel
import Theorems.Thm_TypeDensity_length_quotient_sup_pow_eq_mul
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

theorem TypeDensity.axisQuotientLength_eq (k : Type) [Field k] {s t : Fin 2} (hst : s ≠ t)
    (F : TwoSeries k)
    (d : ℕ) (hlow : ∀ j < d, MvPowerSeries.coeff (Finsupp.single t j) F = 0)
    (hd : MvPowerSeries.coeff (Finsupp.single t d) F ≠ 0) : axisQuotientLength k s F = d := by sorry
