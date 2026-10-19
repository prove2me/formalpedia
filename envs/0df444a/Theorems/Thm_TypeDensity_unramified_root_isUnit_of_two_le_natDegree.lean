-- Prove2me | Theorems.Thm_TypeDensity_unramified_root_isUnit_of_two_le_natDegree
-- name    : TypeDensity.unramified_root_isUnit_of_two_le_natDegree
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:34.538331+00:00
-- url     : https://prove2.me/theorems/0b112957-4525-47fb-8547-fb6d17a939ab
-- title:
--   If `Φ` is an unramified lift of degree at least `2` over a complete local ring with finite residue field, then the root of `Φ` in `O[X]/(Φ)` is a unit.
-- statement:
--   If `Φ` is an unramified lift of degree at least `2` over a complete local ring with finite residue field, then the root of `Φ` in `O[X]/(Φ)` is a unit.
-- source:
--   TypeDensity/Surfaces/Completeness.lean#L274-L292

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_base_ideal_maximal_local
import Theorems.Thm_TypeDensity_residue_extension_equiv
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
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.TotallySplit
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.unramified_root_isUnit_of_two_le_natDegree (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) (h2 : 2 ≤ Φ.natDegree) :
    IsUnit (AdjoinRoot.root Φ) := by sorry
