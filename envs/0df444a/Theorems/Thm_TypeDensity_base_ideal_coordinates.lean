-- Prove2me | Theorems.Thm_TypeDensity_base_ideal_coordinates
-- name    : TypeDensity.base_ideal_coordinates
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:12.54305+00:00
-- url     : https://prove2.me/theorems/91b2545e-58b9-4a9d-8c9f-eeaf3a34f85c
-- title:
--   An element of `O[X]/(Φ)` lies in `(m_O O_δ)^L` iff all its coordinates in the power basis lie in `m_O^L`.
-- statement:
--   An element of `O[X]/(Φ)` lies in `(m_O O_δ)^L` iff all its coordinates in the power basis lie in `m_O^L`.
-- source:
--   TypeDensity/Unramified/Extension.lean#L318-L325

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

theorem TypeDensity.base_ideal_coordinates (O : Type) [CommRing O] [IsLocalRing O] (Φ : Polynomial O)
    (hΦ : Φ.Monic) (L : ℕ) (x : AdjoinRoot Φ) :
    x ∈ (baseIdeal O Φ)^L ↔ ∀ i, (AdjoinRoot.powerBasis' hΦ).basis.repr x i ∈
      (IsLocalRing.maximalIdeal O)^L := by sorry
