-- Prove2me | Theorems.Thm_TypeDensity_forms_linear_bijective
-- name    : TypeDensity.forms_linear_bijective
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:48.936739+00:00
-- url     : https://prove2.me/theorems/f8f6b825-947f-4216-b6d3-a0b33f79612d
-- title:
--   Every binary form of degree `∑ d i` is `∑ h i ∏_{j ≠ i} g j + c ∏ g i` with `h i (ν i) = 0` (partial fractions for pairwise coprime binary forms).
-- statement:
--   Every binary form of degree `∑ d i` is `∑ h i ∏_{j ≠ i} g j + c ∏ g i` with `h i (ν i) = 0` (partial fractions for pairwise coprime binary forms).
-- source:
--   TypeDensity/Unramified/Extension.lean#L865-L953

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Theorems.Thm_TypeDensity_formPoly_add
import Theorems.Thm_TypeDensity_forms_linear_injective
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

theorem TypeDensity.forms_linear_bijective (k ι : Type) [Field k] [Fintype ι] (d : ι → ℕ)
    (g : ∀ i, Fin (d i + 1) → k) (hg : ∀ i, g i ≠ 0) (hc : FormsCoprime d g)
    (ν : ∀ i, Fin (d i + 1)) (hν : ∀ i, g i (ν i) ≠ 0) (w : Fin ((∑ i, d i) + 1) → k) :
    ∃ (h : ∀ i, Fin (d i + 1) → k) (c : k), (∀ i, h i (ν i) = 0) ∧ formPoly w = ∑ i, formPoly
      (h i) * ∏ j ∈ Finset.univ.erase i, formPoly (g j) + Polynomial.C c * ∏ i, formPoly (g i) := by sorry
