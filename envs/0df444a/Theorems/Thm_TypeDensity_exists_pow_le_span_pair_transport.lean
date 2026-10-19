-- Prove2me | Theorems.Thm_TypeDensity_exists_pow_le_span_pair_transport
-- name    : TypeDensity.exists_pow_le_span_pair_transport
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:38.05854+00:00
-- url     : https://prove2.me/theorems/013cac27-41aa-43a2-bd81-924637735b0e
-- title:
--   Finite contact transports along a ring isomorphism `Θ` sending the parameter `e` to a unit multiple of `eT`: if a power of `MS` lies in `(g, e)` and `MT ⊆ Θ(MS)`, then for every `j` a power of `MT` li
-- statement:
--   Finite contact transports along a ring isomorphism `Θ` sending the parameter `e` to a unit multiple of `eT`: if a power of `MS` lies in `(g, e)` and `MT ⊆ Θ(MS)`, then for every `j` a power of `MT` lies in `(Θ g, eT^j)`.
-- source:
--   TypeDensity/Blowup/CurveSections.lean#L896-L914

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
import Theorems.Thm_TypeDensity_sup_pow_le
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
variable {S T : Type} [CommRing S] [CommRing T]

theorem TypeDensity.exists_pow_le_span_pair_transport (Θ : S ≃+* T) {g e : S} {eT u : T} (hu : IsUnit u)
    (he : Θ e * u = eT) {MS : Ideal S} {MT : Ideal T} (hM : MT ≤ MS.map Θ)
    (h : ∃ L, MS ^ L ≤ Ideal.span {g, e ^ 1}) (j : ℕ) :
    ∃ L, MT ^ L ≤ Ideal.span {Θ g, eT ^ j} := by sorry
