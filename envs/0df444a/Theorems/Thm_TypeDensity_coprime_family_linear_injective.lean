-- Prove2me | Theorems.Thm_TypeDensity_coprime_family_linear_injective
-- name    : TypeDensity.coprime_family_linear_injective
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:14.514969+00:00
-- url     : https://prove2.me/theorems/f2a9acc1-e2d1-4291-bbfa-fae794d78407
-- title:
--   For pairwise coprime monic `g i` over a field, `∑ h i ∏_{j ≠ i} g j = 0` with `deg h i < deg g i` forces all `h i = 0`.
-- statement:
--   For pairwise coprime monic `g i` over a field, `∑ h i ∏_{j ≠ i} g j = 0` with `deg h i < deg g i` forces all `h i = 0`.
-- source:
--   TypeDensity/Unramified/Extension.lean#L407-L435

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

theorem TypeDensity.coprime_family_linear_injective (k ι : Type) [Field k] [Fintype ι] (g : ι → Polynomial k)
    (hg : ∀ i, (g i).Monic) (hc : ∀ i j, i ≠ j → IsCoprime (g i) (g j)) (h : ι → Polynomial k)
    (hdeg : ∀ i, (h i).degree < ((g i).natDegree : WithBot ℕ))
    (hsum : ∑ i, h i * ∏ j ∈ Finset.univ.erase i, g j = 0) :
    ∀ i, h i = 0 := by sorry
