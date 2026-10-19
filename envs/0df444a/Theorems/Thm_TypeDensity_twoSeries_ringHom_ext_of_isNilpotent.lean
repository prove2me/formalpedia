-- Prove2me | Theorems.Thm_TypeDensity_twoSeries_ringHom_ext_of_isNilpotent
-- name    : TypeDensity.twoSeries_ringHom_ext_of_isNilpotent
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:27.616114+00:00
-- url     : https://prove2.me/theorems/f2e707b6-ef38-451f-b941-a30a5dec6e95
-- title:
--   Two ring maps out of `O[[T,X]]` that agree on constants, `T` and `X`, and send `T` and `X` to nilpotent elements, are equal.
-- statement:
--   Two ring maps out of `O[[T,X]]` that agree on constants, `T` and `X`, and send `T` and `X` to nilpotent elements, are equal.
-- source:
--   TypeDensity/Surfaces/Completeness.lean#L161-L199

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

theorem TypeDensity.twoSeries_ringHom_ext_of_isNilpotent (O S : Type) [CommRing O] [CommRing S]
    (φ ψ : TwoSeries O →+* S) (hC : ∀ c : O, φ (MvPowerSeries.C c) = ψ (MvPowerSeries.C c))
    (hT : φ (axisT O) = ψ (axisT O)) (hX : φ (axisX O) = ψ (axisX O))
    (hTn : IsNilpotent (φ (axisT O))) (hXn : IsNilpotent (φ (axisX O))) :
    φ = ψ := by sorry
