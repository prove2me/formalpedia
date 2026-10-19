-- Prove2me | Theorems.Thm_TypeDensity_forms_linear_injective
-- name    : TypeDensity.forms_linear_injective
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:06.057359+00:00
-- url     : https://prove2.me/theorems/e2551d59-a37e-4d10-8070-406f5405f407
-- title:
--   Injectivity of the partial-fraction map for pairwise coprime binary forms: if `∑ h i ∏_{j ≠ i} g j = c ∏ g i` with `h i` vanishing at `ν i`, then all `h i = 0`.
-- statement:
--   Injectivity of the partial-fraction map for pairwise coprime binary forms: if `∑ h i ∏_{j ≠ i} g j = c ∏ g i` with `h i` vanishing at `ν i`, then all `h i = 0`.
-- source:
--   TypeDensity/Unramified/Extension.lean#L770-L845

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
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
set_option autoImplicit false

open TypeDensity
open Polynomial IsLocalRing MeasureTheory
open scoped Classical

theorem TypeDensity.forms_linear_injective (k ι : Type) [Field k] [Fintype ι] (d : ι → ℕ)
    (g : ∀ i, Fin (d i + 1) → k) (hg : ∀ i, g i ≠ 0) (hc : FormsCoprime d g)
    (ν : ∀ i, Fin (d i + 1)) (hν : ∀ i, g i (ν i) ≠ 0) (h : ∀ i, Fin (d i + 1) → k)
    (hh : ∀ i, h i (ν i) = 0) (c : k)
    (hsum : ∑ i, formPoly (h i) * ∏ j ∈ Finset.univ.erase i, formPoly (g j) = Polynomial.C c * ∏ i,
      formPoly (g i)) :
    ∀ i, h i = 0 := by sorry
