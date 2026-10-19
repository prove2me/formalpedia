-- Prove2me | Theorems.Thm_TypeDensity_finite_length_module_card
-- name    : TypeDensity.finite_length_module_card
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:16.879232+00:00
-- url     : https://prove2.me/theorems/3dc725da-fac9-4203-887d-b410279d798c
-- title:
--   A module of length `ℓ` over a local ring with finite residue field `k` has `|k|^ℓ` elements.
-- statement:
--   A module of length `ℓ` over a local ring with finite residue field `k` has `|k|^ℓ` elements.
-- source:
--   TypeDensity/Formula/FiniteFieldCounts.lean#L44-L76

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Formula_FiniteFieldCounts
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

theorem TypeDensity.finite_length_module_card (O : Type) [CommRing O] [IsLocalRing O]
    [Finite (IsLocalRing.ResidueField O)] (M : Type) [AddCommGroup M] [Module O M] (ℓ : ℕ)
    (hℓ : Module.length O M = ℓ) :
    Nat.card M = (Nat.card (IsLocalRing.ResidueField O))^ℓ := by sorry
