-- Prove2me | Theorems.Thm_TypeDensity_axisQuotientLength_eq_iff
-- name    : TypeDensity.axisQuotientLength_eq_iff
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:52:41.051011+00:00
-- url     : https://prove2.me/theorems/c3baaa3c-4db5-41f7-98ae-d257b2f7c7ce
-- title:
--   `ℓ(k⟦T, X⟧ ⧸ (F, X_s)) = c` iff the restriction of `F` to the other axis `X_t` has order exactly `c`.
-- statement:
--   `ℓ(k⟦T, X⟧ ⧸ (F, X_s)) = c` iff the restriction of `F` to the other axis `X_t` has order exactly `c`.
-- source:
--   TypeDensity/Surfaces/TruncatedSeries.lean#L139-L154

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Surfaces_TruncatedSeries
import Theorems.Thm_TypeDensity_axisQuotientLength_eq_top
import Theorems.Thm_TypeDensity_axisQuotientLength_eq
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

theorem TypeDensity.axisQuotientLength_eq_iff (k : Type) [Field k] {s t : Fin 2} (hst : s ≠ t) (F : TwoSeries k)
    (c : ℕ) : axisQuotientLength k s F = c ↔
      (∀ j < c, MvPowerSeries.coeff (Finsupp.single t j) F = 0) ∧
      MvPowerSeries.coeff (Finsupp.single t c) F ≠ 0 := by sorry
