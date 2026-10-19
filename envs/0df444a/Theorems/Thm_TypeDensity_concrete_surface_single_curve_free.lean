-- Prove2me | Theorems.Thm_TypeDensity_concrete_surface_single_curve_free
-- name    : TypeDensity.concrete_surface_single_curve_free
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:31:33.193092+00:00
-- url     : https://prove2.me/theorems/0bf16570-4d91-449f-a288-a100fd0f50da
-- title:
--   On the concrete surface with `b = 0`, if `f` reduces to a function of positive finite contact `c` with the special fiber axis, then `O[f]` is free of rank `a * c` over `O`.
-- statement:
--   On the concrete surface with `b = 0`, if `f` reduces to a function of positive finite contact `c` with the special fiber axis, then `O[f]` is free of rank `a * c` over `O`.
-- source:
--   TypeDensity/Blowup/StrictNormalizer.lean#L673-L708

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
import Theorems.Thm_TypeDensity_concrete_surface_special_fiber_length_transport
import Theorems.Thm_TypeDensity_special_fiber_single_contact_regular
import Theorems.Thm_TypeDensity_concrete_surface_residue_regular_of_special_fiber
import Theorems.Thm_TypeDensity_concrete_surface_curve_free_of_length
import Theorems.Thm_TypeDensity_single_special_fiber_length
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

theorem TypeDensity.concrete_surface_single_curve_free (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (pi : O)
    (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a : ℕ) (ha : 0 < a)
    (f : ConcreteSurface O pi u a 0)
    (e : (ConcreteSurface O pi u a 0 ⧸ Ideal.span {algebraMap O (ConcreteSurface O pi u a 0) pi})
    ≃+* SpecialFiber (IsLocalRing.ResidueField O) a 0) (c : ℕ) (hc : 0 < c)
    (hcontact : contact
    (e (Ideal.Quotient.mk (Ideal.span {algebraMap O (ConcreteSurface O pi u a 0) pi}) f))
    (fiberT (IsLocalRing.ResidueField O) a 0) = c) :
    Module.Free O (ConcreteSurface O pi u a 0 ⧸ Ideal.span {f}) ∧ Module.Finite O
      (ConcreteSurface O pi u a 0 ⧸ Ideal.span {f}) ∧ Module.finrank O
      (ConcreteSurface O pi u a 0 ⧸ Ideal.span {f}) = a*c := by sorry
