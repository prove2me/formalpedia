-- Prove2me | Theorems.Thm_TypeDensity_unramified_is_dvr
-- name    : TypeDensity.unramified_is_dvr
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:23.072988+00:00
-- url     : https://prove2.me/theorems/56cf1cdc-b539-4e83-ac29-acca8571612e
-- title:
--   For an unramified lift `Φ`, `O[X]/(Φ)` is a complete DVR with maximal ideal `𝔪 O[X]/(Φ)`, in which every uniformizer of `O` stays a uniformizer, with finite residue field of cardinality `q ^ deg Φ`.
-- statement:
--   For an unramified lift `Φ`, `O[X]/(Φ)` is a complete DVR with maximal ideal `𝔪 O[X]/(Φ)`, in which every uniformizer of `O` stays a uniformizer, with finite residue field of cardinality `q ^ deg Φ`.
-- source:
--   TypeDensity/Unramified/FrobeniusDescent.lean#L801-L837

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_unramified_adic_complete
import Theorems.Thm_TypeDensity_base_ideal_maximal_local
import Theorems.Thm_TypeDensity_unramified_is_domain
import Theorems.Thm_TypeDensity_residue_extension_field
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
import Mathlib.RingTheory.Henselian
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.unramified_is_dvr (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) :
    ∃ (_ : IsDomain (AdjoinRoot Φ)) (_ : IsLocalRing (AdjoinRoot Φ)),
      IsDiscreteValuationRing (AdjoinRoot Φ) ∧
      IsLocalRing.maximalIdeal (AdjoinRoot Φ) = baseIdeal O Φ ∧
      (∀ ϖ : O, Irreducible ϖ → Irreducible (algebraMap O (AdjoinRoot Φ) ϖ)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (AdjoinRoot Φ)) (AdjoinRoot Φ) ∧
      Finite (IsLocalRing.ResidueField (AdjoinRoot Φ)) ∧
      Nat.card (IsLocalRing.ResidueField (AdjoinRoot Φ)) = residueCard O ^ Φ.natDegree := by sorry
