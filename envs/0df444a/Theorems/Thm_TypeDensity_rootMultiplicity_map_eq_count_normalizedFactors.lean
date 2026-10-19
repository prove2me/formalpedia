-- Prove2me | Theorems.Thm_TypeDensity_rootMultiplicity_map_eq_count_normalizedFactors
-- name    : TypeDensity.rootMultiplicity_map_eq_count_normalizedFactors
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:40.908308+00:00
-- url     : https://prove2.me/theorems/cad29d7e-99aa-40f2-89b5-b5b5f42daa6f
-- title:
--   Over a finite field `k`, if `ᾱ` is a root of the monic irreducible `φ` in an extension `k'`, then the multiplicity of `ᾱ` as a root of `G` equals the multiplicity of `φ` among the normalized factors o
-- statement:
--   Over a finite field `k`, if `ᾱ` is a root of the monic irreducible `φ` in an extension `k'`, then the multiplicity of `ᾱ` as a root of `G` equals the multiplicity of `φ` among the normalized factors of `G`.
-- source:
--   TypeDensity/Blowup/ExceptionalLayers.lean#L789-L840

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
open scoped Classical
open Polynomial UniqueFactorizationMonoid

theorem TypeDensity.rootMultiplicity_map_eq_count_normalizedFactors (k k' : Type) [Field k] [Finite k]
    [Field k'] (ι : k →+* k') (G : Polynomial k) (hG : G ≠ 0) (φ : Polynomial k)
    (hφ : φ.Monic ∧ Irreducible φ) (alphaBar : k') (hroot : (φ.map ι).eval alphaBar = 0) :
    Polynomial.rootMultiplicity alphaBar (G.map ι) = Multiset.count φ
    (UniqueFactorizationMonoid.normalizedFactors G) := by sorry
