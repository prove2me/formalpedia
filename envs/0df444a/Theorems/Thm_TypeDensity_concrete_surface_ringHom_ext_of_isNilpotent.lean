-- Prove2me | Theorems.Thm_TypeDensity_concrete_surface_ringHom_ext_of_isNilpotent
-- name    : TypeDensity.concrete_surface_ringHom_ext_of_isNilpotent
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:00.431856+00:00
-- url     : https://prove2.me/theorems/43a21a83-527c-4b1a-877a-bcced897ba6d
-- title:
--   Two ring maps out of the concrete surface that agree on constants, `t` and `x`, and send `t` and `x` to nilpotent elements, are equal.
-- statement:
--   Two ring maps out of the concrete surface that agree on constants, `t` and `x`, and send `t` and `x` to nilpotent elements, are equal.
-- source:
--   TypeDensity/Surfaces/Completeness.lean#L201-L212

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
import Theorems.Thm_TypeDensity_twoSeries_ringHom_ext_of_isNilpotent
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

theorem TypeDensity.concrete_surface_ringHom_ext_of_isNilpotent (O S : Type) [CommRing O] [CommRing S]
    (pi : O) (u : (TwoSeries O)ˣ) (a b : ℕ) (φ ψ : ConcreteSurface O pi u a b →+* S)
    (hC : ∀ c : O, φ (algebraMap O (ConcreteSurface O pi u a b) c) =
      ψ (algebraMap O (ConcreteSurface O pi u a b) c))
    (hT : φ (surfaceT O pi u a b) = ψ (surfaceT O pi u a b))
    (hX : φ (surfaceX O pi u a b) = ψ (surfaceX O pi u a b))
    (hTn : IsNilpotent (φ (surfaceT O pi u a b))) (hXn : IsNilpotent (φ (surfaceX O pi u a b))) :
    φ = ψ := by sorry
