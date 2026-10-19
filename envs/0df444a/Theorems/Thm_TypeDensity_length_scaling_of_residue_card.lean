-- Prove2me | Theorems.Thm_TypeDensity_length_scaling_of_residue_card
-- name    : TypeDensity.length_scaling_of_residue_card
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:21.612312+00:00
-- url     : https://prove2.me/theorems/c4f58feb-47fe-467b-96c7-956c8194a035
-- title:
--   If `#k(O') = #k(O) ^ δ`, then a module of `O'`-length `ℓ` has `O`-length `δ ℓ`.
-- statement:
--   If `#k(O') = #k(O) ^ δ`, then a module of `O'`-length `ℓ` has `O`-length `δ ℓ`.
-- source:
--   TypeDensity/Measure/Normalizer.lean#L323-L342

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Formula_FiniteFieldCounts
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Definitions.Def_TypeDensity_Surfaces_TruncatedSeries
import Theorems.Thm_TypeDensity_finite_length_module_card
import Theorems.Thm_TypeDensity_finite_module_length_card
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
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.length_scaling_of_residue_card (O : Type) [CommRing O] [IsLocalRing O]
    [Finite (IsLocalRing.ResidueField O)] (O' : Type) [CommRing O'] [IsLocalRing O']
    [Finite (IsLocalRing.ResidueField O')] (δ : ℕ)
    (hδ : Nat.card (IsLocalRing.ResidueField O') = Nat.card (IsLocalRing.ResidueField O) ^ δ)
    (M : Type) [AddCommGroup M] [Module O M] [Module O' M] (ℓ : ℕ) (hℓ : Module.length O' M = ℓ) :
    Module.length O M = ((δ * ℓ : ℕ) : ℕ∞) := by sorry
