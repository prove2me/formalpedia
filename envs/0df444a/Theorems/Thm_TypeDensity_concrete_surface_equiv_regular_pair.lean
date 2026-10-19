-- Prove2me | Theorems.Thm_TypeDensity_concrete_surface_equiv_regular_pair
-- name    : TypeDensity.concrete_surface_equiv_regular_pair
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:08.18421+00:00
-- url     : https://prove2.me/theorems/01c0d1b7-f950-47bd-a9dc-93f1f2b367b7
-- title:
--   In a ring isomorphic to a concrete surface, the images of `(t, x)` and `(x, t)` are regular parameter pairs;
-- statement:
--   In a ring isomorphic to a concrete surface, the images of `(t, x)` and `(x, t)` are regular parameter pairs; in particular `t` is a non-zero-divisor.
-- source:
--   TypeDensity/Surfaces/Regularity.lean#L298-L310

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_concrete_surface_regular_pair_tx
import Theorems.Thm_TypeDensity_concrete_surface_regular_pair_xt
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
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.concrete_surface_equiv_regular_pair (S : Type) [CommRing S] (O' : Type) [CommRing O']
    [IsDomain O'] [IsDiscreteValuationRing O'] (pi' : O') (hpi' : Irreducible pi')
    (u' : (TwoSeries O')ˣ) (a' b' : ℕ) (ha' : 0 < a') (Eq : S ≃+* ConcreteSurface O' pi' u' a' b') :
    RegularParameterPair S (Eq.symm (surfaceT O' pi' u' a' b'))
      (Eq.symm (surfaceX O' pi' u' a' b')) ∧ RegularParameterPair S
      (Eq.symm (surfaceX O' pi' u' a' b')) (Eq.symm (surfaceT O' pi' u' a' b')) ∧ Function.Injective
      (fun y : S ↦ Eq.symm (surfaceT O' pi' u' a' b') * y) := by sorry
