-- Prove2me | Theorems.Thm_TypeDensity_base_ideal_pure
-- name    : TypeDensity.base_ideal_pure
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:39.743983+00:00
-- url     : https://prove2.me/theorems/58e7a894-af7f-4b92-9a30-2880ebc096f0
-- title:
--   A base element `c ∈ O` lies in `(m_O O_δ)^L` iff `c ∈ m_O^L` (for `Φ` monic of positive degree).
-- statement:
--   A base element `c ∈ O` lies in `(m_O O_δ)^L` iff `c ∈ m_O^L` (for `Φ` monic of positive degree).
-- source:
--   TypeDensity/Unramified/Extension.lean#L327-L346

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Theorems.Thm_TypeDensity_base_ideal_coordinates
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

theorem TypeDensity.base_ideal_pure (O : Type) [CommRing O] [IsLocalRing O] (Φ : Polynomial O) (hΦ : Φ.Monic)
    (hdeg : 0 < Φ.natDegree) (L : ℕ) (c : O) :
    algebraMap O (AdjoinRoot Φ) c ∈ (baseIdeal O Φ)^L ↔ c ∈ (IsLocalRing.maximalIdeal O)^L := by sorry
