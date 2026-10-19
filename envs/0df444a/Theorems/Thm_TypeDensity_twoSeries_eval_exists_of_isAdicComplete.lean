-- Prove2me | Theorems.Thm_TypeDensity_twoSeries_eval_exists_of_isAdicComplete
-- name    : TypeDensity.twoSeries_eval_exists_of_isAdicComplete
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:14.908599+00:00
-- url     : https://prove2.me/theorems/89b55a00-87e9-4f99-8b15-f9c4d0acfa87
-- title:
--   Over a ring `S` complete for an ideal `I`, any ring map `O' → S` extends to an evaluation `O'[[T,X]] → S` sending `T ↦ e` and `X ↦ z` for given `e, z ∈ I`.
-- statement:
--   Over a ring `S` complete for an ideal `I`, any ring map `O' → S` extends to an evaluation `O'[[T,X]] → S` sending `T ↦ e` and `X ↦ z` for given `e, z ∈ I`.
-- source:
--   TypeDensity/Surfaces/Completeness.lean#L214-L249

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
import Theorems.Thm_TypeDensity_nilpotentEval_apply_generators
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

theorem TypeDensity.twoSeries_eval_exists_of_isAdicComplete (S : Type) [CommRing S] (I : Ideal S)
    [IsAdicComplete I S] (O' : Type) [CommRing O'] (κ : O' →+* S) (e z : S) (he : e ∈ I)
    (hz : z ∈ I) :
    ∃ Θ : TwoSeries O' →+* S,
      (∀ c : O', Θ (MvPowerSeries.C c) = κ c) ∧ Θ (axisT O') = e ∧ Θ (axisX O') = z := by sorry
