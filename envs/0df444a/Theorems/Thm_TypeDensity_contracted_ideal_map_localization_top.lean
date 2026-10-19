-- Prove2me | Theorems.Thm_TypeDensity_contracted_ideal_map_localization_top
-- name    : TypeDensity.contracted_ideal_map_localization_top
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:36.396383+00:00
-- url     : https://prove2.me/theorems/3b8f04a3-dd84-4fb3-b055-f19806d9bb03
-- title:
--   If `P^L ⊆ I` and `P` meets the localizing submonoid, then `I` extends to the unit ideal.
-- statement:
--   If `P^L ⊆ I` and `P` meets the localizing submonoid, then `I` extends to the unit ideal.
-- source:
--   TypeDensity/Blowup/Charts.lean#L1108-L1115

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
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
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.contracted_ideal_map_localization_top (A S : Type) [CommRing A] [CommRing S] [Algebra A S]
    (M : Submonoid A) [IsLocalization M S] (P I : Ideal A) (L : ℕ) (hPI : P ^ L ≤ I) (m : A)
    (hm : m ∈ M) (hmP : m ∈ P) :
    I.map (algebraMap A S) = ⊤ := by sorry
