-- Prove2me | Theorems.Thm_TypeDensity_surjective_ker_comp_quotient_equiv
-- name    : TypeDensity.surjective_ker_comp_quotient_equiv
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:32.804349+00:00
-- url     : https://prove2.me/theorems/ce204116-fbfc-4586-8d65-09d32207404d
-- title:
--   Composing a ring isomorphism `E : S ≃+* T` with the projection onto `T ⧸ (y)` and an isomorphism `q` of that quotient with `k⟦X⟧` gives a surjection with kernel `(w)`, where `E w = y`.
-- statement:
--   Composing a ring isomorphism `E : S ≃+* T` with the projection onto `T ⧸ (y)` and an isomorphism `q` of that quotient with `k⟦X⟧` gives a surjection with kernel `(w)`, where `E w = y`.
-- source:
--   TypeDensity/Blowup/NilpotentGluing.lean#L1336-L1349

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
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.Algebra.Group.NatPowAssoc
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.surjective_ker_comp_quotient_equiv {S T k : Type} [CommRing S] [CommRing T]
    [Field k] (E : S ≃+* T) (y : T) (q : (T ⧸ Ideal.span {y}) ≃+* PowerSeries k) (w : S)
    (hw : E w = y) :
    Function.Surjective (q.toRingHom.comp ((Ideal.Quotient.mk (Ideal.span {y})).comp E.toRingHom)) ∧
    RingHom.ker (q.toRingHom.comp ((Ideal.Quotient.mk (Ideal.span {y})).comp E.toRingHom)) =
      Ideal.span {w} := by sorry
