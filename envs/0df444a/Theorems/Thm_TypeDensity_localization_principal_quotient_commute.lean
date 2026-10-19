-- Prove2me | Theorems.Thm_TypeDensity_localization_principal_quotient_commute
-- name    : TypeDensity.localization_principal_quotient_commute
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:46.378156+00:00
-- url     : https://prove2.me/theorems/04bd1a28-1b0b-4136-9698-b8bc6b10671c
-- title:
--   Localizing at `z` commutes with taking the principal power quotient `A ⧸ (e)^j`.
-- statement:
--   Localizing at `z` commutes with taking the principal power quotient `A ⧸ (e)^j`.
-- source:
--   TypeDensity/Blowup/PointTransport.lean#L254-L309

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
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.localization_principal_quotient_commute (A : Type) [CommRing A] (e z : A) (j : ℕ) :
    ∃ L : PrincipalPowerQuotient (Localization.Away z)
    (algebraMap A (Localization.Away z) e) j ≃+* Localization.Away
    (Ideal.Quotient.mk ((Ideal.span {e})^j) z), ∀ a : A, L
    (Ideal.Quotient.mk ((Ideal.span {algebraMap A (Localization.Away z) e})^j)
      (algebraMap A (Localization.Away z) a)) = algebraMap (PrincipalPowerQuotient A e j)
    (Localization.Away (Ideal.Quotient.mk ((Ideal.span {e})^j) z))
    (Ideal.Quotient.mk ((Ideal.span {e})^j) a) := by sorry
